"""
今彩539 每日自動更新與多維度抓牌推薦系統 (88期滾動 + 冷門破冰 + 火焰高機率判定版)
====================================================================================
功能：
1. 自動抓取與合併歷史資料（114 年至今，並支援每日 21:35 自動更新）。
2. 以最新一期往前滾動「88 期」為基準，產出：
   - 每日推薦固定 7 碼（綜合權重排序）
   - 獨支 1～2 支（單支在 88 期內固定間隔週期出現頻率最高者）
   - 週期規律牌組（隔 3～5 期拖牌 + 前導號帶出固定雙星）
   - 每日土地公幸運號碼 1 碼（嚴格排除推薦主牌與獨支後挑選，不重複）
   - AI 高機率火焰框判定（僅當系統判定綜合機率達高標門檻時標記火焰框，否則不標記）
   - 近 88 期最久未開 Top 5 冷門追蹤，若開出則自動移出並記錄「幾期沒開、於哪天開出」
3. 自動對獎與紀錄留存（標註土地公／獨支／推薦 7 碼命中顆數）。
"""

from __future__ import annotations

import argparse
import csv
import datetime as dt
import hashlib
import itertools
import json
import re
import urllib.request
from collections import Counter, defaultdict
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Set, Tuple


@dataclass
class DrawRecord:
    draw_date: str
    period: str
    numbers: Tuple[int, int, int, int, int]


PILIO_URL = "https://www.pilio.idv.tw/lto539/list539APP.asp"
LOTTO8_URL = "https://www.lotto-8.com/listlto539.asp"


def fetch_from_lotto8(max_pages: int = 10) -> List[DrawRecord]:
    records: List[DrawRecord] = []
    headers = {
        "User-Agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36"
        )
    }
    row_pattern = re.compile(
        r"(\d{4})/(\d{2})/(\d{2})\D{1,20}(\d{2})[,\s]+(\d{2})[,\s]+(\d{2})[,\s]+(\d{2})[,\s]+(\d{2})"
    )
    for page in range(1, max_pages + 1):
        url = f"{LOTTO8_URL}?indexpage={page}&orderby=new"
        req = urllib.request.Request(url, headers=headers)
        with urllib.request.urlopen(req, timeout=15) as resp:
            html = resp.read().decode("utf-8", errors="ignore")
        text = re.sub(r"\s+", " ", re.sub(r"<[^>]+>", " ", html))
        matches = row_pattern.findall(text)
        if not matches:
            break
        for yyyy, mm, dd, n1, n2, n3, n4, n5 in matches:
            date_str = f"{int(yyyy):04d}-{int(mm):02d}-{int(dd):02d}"
            nums = tuple(sorted(int(x) for x in (n1, n2, n3, n4, n5)))
            if len(nums) == 5 and all(1 <= n <= 39 for n in nums):
                records.append(DrawRecord(draw_date=date_str, period="", numbers=nums))
    return deduplicate_and_sort(records)


def fetch_from_pilio(max_pages: int = 26) -> List[DrawRecord]:
    records: List[DrawRecord] = []
    headers = {
        "User-Agent": (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
            "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/128.0.0.0 Safari/537.36"
        )
    }
    row_pattern = re.compile(
        r"(\d{2})/(\d{2})\s+(\d{2})\([一二三四五六日]\).*?"
        r"(\d{2}),\s*(\d{2}),\s*(\d{2}),\s*(\d{2}),\s*(\d{2})",
        re.S,
    )
    for page in range(1, max_pages + 1):
        url = f"{PILIO_URL}?indexpage={page}&orderby=new"
        req = urllib.request.Request(url, headers=headers)
        with urllib.request.urlopen(req, timeout=15) as resp:
            html = resp.read().decode("utf-8", errors="ignore")
        text = re.sub(r"\s+", " ", re.sub(r"<[^>]+>", " ", html))
        matches = row_pattern.findall(text)
        if not matches:
            break
        for mm, dd, yy, n1, n2, n3, n4, n5 in matches:
            date_str = f"{2000 + int(yy):04d}-{int(mm):02d}-{int(dd):02d}"
            nums = tuple(sorted(int(x) for x in (n1, n2, n3, n4, n5)))
            if len(nums) == 5 and all(1 <= n <= 39 for n in nums):
                records.append(DrawRecord(draw_date=date_str, period="", numbers=nums))
    return deduplicate_and_sort(records)


def deduplicate_and_sort(records: Sequence[DrawRecord]) -> List[DrawRecord]:
    by_date: Dict[str, DrawRecord] = {}
    for rec in records:
        existing = by_date.get(rec.draw_date)
        if existing is None or (not existing.period and rec.period):
            by_date[rec.draw_date] = rec
    return [by_date[d] for d in sorted(by_date.keys())]


def filter_since_114(records: Sequence[DrawRecord]) -> List[DrawRecord]:
    return [r for r in records if r.draw_date >= "2025-01-01"]


class Rolling88Analyzer:
    BASELINE_PROB = 5.0 / 39.0
    FLAME_SCORE_THRESHOLD = 75.0

    def __init__(self, all_records: Sequence[DrawRecord], window: int = 88):
        self.all_records = deduplicate_and_sort(all_records)
        if len(self.all_records) < 15:
            raise ValueError("歷史開獎期數過少，至少需要 15 期以上。")
        self.window = min(window, len(self.all_records))
        self.records = self.all_records[-self.window :]

    def analyze_coldest_and_icebreakers(self, top_n: int = 5) -> Dict[str, object]:
        """統計近 88 期最久未開前 5 碼，並追蹤近期從該榜單破冰開出的號碼。"""
        n_draws = len(self.records)
        cold_list = []
        for num in range(1, 40):
            last_idx = -1
            for idx in range(n_draws - 1, -1, -1):
                if num in self.records[idx].numbers:
                    last_idx = idx
                    break
            omitted = (n_draws - 1 - last_idx) if last_idx != -1 else n_draws
            last_date = self.records[last_idx].draw_date if last_idx != -1 else f"超過{n_draws}期未開"
            cold_list.append(
                {
                    "number": num,
                    "formatted": f"{num:02d}",
                    "omitted_draws": omitted,
                    "last_seen_date": last_date,
                }
            )

        # 排除最新一期剛開出的號碼（omitted == 0），取最久沒開的前 5 個
        cold_top5 = sorted(
            [c for c in cold_list if c["omitted_draws"] > 0],
            key=lambda x: (-x["omitted_draws"], x["number"]),  # type: ignore[operator]
        )[:top_n]

        # 掃描最近 15 期開獎中，哪些原本是「前一期最久未開 Top 5」或遺漏 >= 15 期的號碼破冰開出
        icebreakers = []
        scan_start = max(1, len(self.all_records) - 15)
        for idx in range(len(self.all_records) - 1, scan_start - 1, -1):
            cur = self.all_records[idx]
            prev_win = self.all_records[max(0, idx - self.window) : idx]
            if not prev_win:
                continue
            # 計算開獎前這 88 期的遺漏排行
            prev_omitted = {}
            for num in range(1, 40):
                lp = -1
                for j in range(len(prev_win) - 1, -1, -1):
                    if num in prev_win[j].numbers:
                        lp = j
                        break
                prev_omitted[num] = (len(prev_win) - 1 - lp) if lp != -1 else len(prev_win)
            prev_top5_set = {
                k for k, _ in sorted(prev_omitted.items(), key=lambda kv: (-kv[1], kv[0]))[:top_n]
            }
            for num in cur.numbers:
                if num in prev_top5_set:
                    icebreakers.append(
                        {
                            "number": num,
                            "formatted": f"{num:02d}",
                            "omitted_before_hit": prev_omitted[num],
                            "hit_date": cur.draw_date,
                        }
                    )

        return {"cold_top5": cold_top5, "icebreakers": icebreakers[:15]}

    def analyze_solo_numbers(self, top_n: int = 2) -> List[Dict[str, object]]:
        total = len(self.records)
        solo_candidates: List[Dict[str, object]] = []
        for num in range(1, 40):
            positions = [idx for idx, rec in enumerate(self.records) if num in rec.numbers]
            freq = len(positions)
            if freq < 4:
                continue
            gaps = [positions[i] - positions[i - 1] for i in range(1, len(positions))]
            best_gap, best_gap_hits = Counter(gaps).most_common(1)[0]
            draws_since_last = (total - 1) - positions[-1]
            recent_30 = sum(1 for p in positions if p >= max(0, total - 30))
            if draws_since_last + 1 == best_gap:
                cycle_match_bonus = 45.0
            elif abs((draws_since_last + 1) - best_gap) <= 1:
                cycle_match_bonus = 22.0
            elif draws_since_last == 0 and best_gap > 1:
                cycle_match_bonus = -15.0
            else:
                cycle_match_bonus = 0.0
            regularity_ratio = best_gap_hits / max(len(gaps), 1)
            score = freq * 1.0 + recent_30 * 3.0 + best_gap_hits * 3.5 + regularity_ratio * 18.0 + cycle_match_bonus
            solo_candidates.append(
                {
                    "number": num,
                    "formatted": f"{num:02d}",
                    "freq_in_88": freq,
                    "best_interval": best_gap,
                    "interval_hits": best_gap_hits,
                    "draws_since_last": draws_since_last,
                    "score": round(score, 1),
                    "reason": f"近{self.window}期開{freq}次，間隔{best_gap}期規律出現{best_gap_hits}次（已隔{draws_since_last}期）",
                }
            )
        solo_candidates.sort(key=lambda x: x["score"], reverse=True)  # type: ignore[arg-type]
        return solo_candidates[:top_n]

    def analyze_cycle_rules(self, lag_min: int = 3, lag_max: int = 5) -> Dict[str, object]:
        n_draws = len(self.records)
        lag_scores: Dict[int, float] = defaultdict(float)
        lag_rules: List[Dict[str, object]] = []

        for lag in range(lag_min, lag_max + 1):
            if n_draws <= lag:
                continue
            triggers = self.records[-lag].numbers
            trig_total: Counter[int] = Counter()
            follow_cnt: Dict[int, Counter[int]] = defaultdict(Counter)
            for i in range(n_draws - lag):
                for a in self.records[i].numbers:
                    trig_total[a] += 1
                    for b in self.records[i + lag].numbers:
                        follow_cnt[a][b] += 1
            for a in triggers:
                tot = trig_total[a]
                if tot < 3:
                    continue
                for b, cnt in follow_cnt[a].most_common(3):
                    prob = cnt / tot
                    lift = prob / self.BASELINE_PROB
                    if cnt >= 2 and lift >= 1.2:
                        lag_scores[b] += (lift - 1.0) * 12.0 + cnt * 1.5
                        lag_rules.append(
                            {
                                "trigger": f"{a:02d}",
                                "trigger_date": self.records[-lag].draw_date,
                                "lag": lag,
                                "target": f"{b:02d}",
                                "hits": cnt,
                                "total": tot,
                                "probability": round(prob, 4),
                                "lift": round(lift, 2),
                            }
                        )
        lag_rules.sort(key=lambda x: (x["hits"], x["lift"]), reverse=True)  # type: ignore[arg-type]

        lead_pair_hits: Dict[Tuple[int, Tuple[int, int]], int] = Counter()
        lead_total: Counter[int] = Counter()
        for i in range(n_draws - 1):
            horizon = sorted({x for j in range(i + 1, min(i + 6, n_draws)) for x in self.records[j].numbers})
            pairs_in_horizon = list(itertools.combinations(horizon, 2))
            for a in self.records[i].numbers:
                lead_total[a] += 1
                for p in pairs_in_horizon:
                    lead_pair_hits[(a, p)] += 1

        recent_3_nums = {x for rec in self.records[-3:] for x in rec.numbers}
        repeating_patterns: List[Dict[str, object]] = []
        for (a, pair), cnt in lead_pair_hits.most_common(120):
            if cnt >= 4 and lead_total[a] >= 5:
                rate = cnt / lead_total[a]
                if a in recent_3_nums:
                    lag_scores[pair[0]] += cnt * 0.8
                    lag_scores[pair[1]] += cnt * 0.8
                repeating_patterns.append(
                    {
                        "lead": f"{a:02d}",
                        "active_now": a in recent_3_nums,
                        "pair": [f"{pair[0]:02d}", f"{pair[1]:02d}"],
                        "hits": cnt,
                        "lead_occurrences": lead_total[a],
                        "hit_rate": round(rate, 3),
                    }
                )
        repeating_patterns.sort(key=lambda x: (x["active_now"], x["hits"], x["hit_rate"]), reverse=True)  # type: ignore[arg-type]
        return {"lag_3_to_5_rules": lag_rules[:12], "repeating_lead_pairs": repeating_patterns[:10], "cycle_scores": dict(lag_scores)}

    def compute_tudigong_number(self, target_date: str, exclude_numbers: Set[int]) -> Dict[str, object]:
        """排除推薦主牌與獨支後，從剩餘溫熱號碼池挑出 1 個土地公幸運號碼（與網頁端 FNV-1a 完全同步）。"""
        freq = Counter()
        for rec in self.records:
            freq.update(rec.numbers)
        ordered = sorted(
            [n for n in range(1, 40) if n not in exclude_numbers],
            key=lambda n: (-freq[n], n),
        )
        # 優先取排除後的溫熱中段區間
        pool = ordered[4:20] if len(ordered) >= 20 else ordered
        key = f"TUDIGONG-539-{target_date}"
        h = 2166136261
        for ch in key:
            h ^= ord(ch)
            h = (h * 16777619) & 0xFFFFFFFF
        pick = pool[h % len(pool)]
        return {
            "number": pick,
            "formatted": f"{pick:02d}",
            "target_date": target_date,
            "freq_in_88": freq[pick],
            "note": f"已排除推薦主牌與獨支，依 {target_date} 土地公吉數定號（近88期開 {freq[pick]} 次）",
        }

    def analyze_tail_and_big_small(self, top_rec_numbers: Sequence[int]) -> Dict[str, object]:
        n_draws = len(self.records)
        tail_counts = [0] * 10
        tail_last_seen = [-1] * 10
        big_cnt = small_cnt = tie_cnt = sum_total = 0

        for idx, rec in enumerate(self.records):
            b = s = 0
            for num in rec.numbers:
                t = num % 10
                tail_counts[t] += 1
                tail_last_seen[t] = idx
                sum_total += num
                if num >= 21:
                    b += 1
                elif num <= 19:
                    s += 1
            if b > s:
                big_cnt += 1
            elif s > b:
                small_cnt += 1
            else:
                tie_cnt += 1

        rec_bonus = [0] * 10
        for n in top_rec_numbers:
            rec_bonus[n % 10] += 8

        tail_list = []
        for t in range(10):
            omitted = (n_draws - 1 - tail_last_seen[t]) if tail_last_seen[t] != -1 else n_draws
            score = round(tail_counts[t] * 1.2 + omitted * 3.5 + rec_bonus[t], 1)
            nums = [f"{k:02d}" for k in range(10 if t == 0 else t, 40, 10)]
            tail_list.append({"tail": t, "count": tail_counts[t], "omitted": omitted, "score": score, "nums": nums})
        tail_list.sort(key=lambda x: x["score"], reverse=True)  # type: ignore[arg-type]

        return {
            "best_tail": tail_list[0],
            "top3_tails": tail_list[:3],
            "big_small": {
                "big_count": big_cnt,
                "small_count": small_cnt,
                "tie_count": tie_cnt,
                "big_prob": round((big_cnt / n_draws) * 100, 1),
                "small_prob": round((small_cnt / n_draws) * 100, 1),
                "tie_prob": round((tie_cnt / n_draws) * 100, 1),
                "avg_sum": round(sum_total / n_draws, 1),
            },
        }

    def generate_prediction(self, target_date: str, top_k: int = 7) -> Dict[str, object]:
        solo = self.analyze_solo_numbers(top_n=2)
        cycles = self.analyze_cycle_rules(lag_min=3, lag_max=5)
        cold_info = self.analyze_coldest_and_icebreakers(top_n=5)

        pair_counts: Counter[Tuple[int, int]] = Counter()
        for rec in self.records:
            for p in itertools.combinations(rec.numbers, 2):
                pair_counts[p] += 1
        latest_set = set(self.records[-1].numbers)
        co_scores: Dict[int, float] = defaultdict(float)
        for pair, cnt in pair_counts.most_common(50):
            hit = latest_set.intersection(pair)
            if len(hit) == 1:
                miss = next(x for x in pair if x not in latest_set)
                co_scores[miss] += cnt

        solo_map = {s["number"]: float(s["score"]) for s in solo}  # type: ignore[arg-type]
        cyc_map: Dict[int, float] = cycles["cycle_scores"]  # type: ignore[assignment]

        def norm(m: Dict[int, float]) -> Dict[int, float]:
            mx = max(m.values()) if m else 0.0
            return {n: (m.get(n, 0.0) / mx if mx > 0 else 0.0) for n in range(1, 40)}

        n_co = norm(co_scores)
        n_cy = norm(cyc_map)
        n_so = norm(solo_map)

        ranked = []
        for n in range(1, 40):
            score = round((0.45 * n_cy[n] + 0.30 * n_co[n] + 0.25 * n_so[n]) * 100, 1)
            active_signals = sum([n_cy[n] >= 0.4, n_co[n] >= 0.4, n_so[n] >= 0.4])
            # AI 火焰判定：綜合評分 >= 75 且至少 2 項訊號同時成立
            is_flame = score >= self.FLAME_SCORE_THRESHOLD and active_signals >= 2
            ranked.append(
                {
                    "number": n,
                    "formatted": f"{n:02d}",
                    "score": score,
                    "is_flame": is_flame,
                }
            )
        ranked.sort(key=lambda x: x["score"], reverse=True)  # type: ignore[arg-type]

        top_recs = ranked[:top_k]
        # 固定排除前 8 碼與獨支，確保切換 7 碼或 8 碼時土地公號碼完全一致
        exclude_set = {r["number"] for r in ranked[:8]} | {s["number"] for s in solo}  # type: ignore[misc]
        tudigong = self.compute_tudigong_number(target_date, exclude_numbers=exclude_set)  # type: ignore[arg-type]
        tudi_item = next(r for r in ranked if r["number"] == tudigong["number"])
        tudi_high_prob = float(tudi_item["score"]) >= 50.0  # type: ignore[arg-type]
        tudigong["is_flame"] = tudi_high_prob
        tudigong["ai_score"] = tudi_item["score"]
        flame_numbers = [tudigong["formatted"]] if tudi_high_prob else []

        return {
            "target_date": target_date,
            "based_on_last_draw": self.records[-1].draw_date,
            "window_draws": self.window,
            "recommended_numbers": [r["formatted"] for r in top_recs],
            "recommended_details": top_recs,
            "ai_flame_numbers": flame_numbers,
            "solo_numbers": solo,
            "tudigong_number": tudigong,
            "tail_and_bs": self.analyze_tail_and_big_small([r["number"] for r in top_recs]),
            "cold_tracking": cold_info,
            "cycle_patterns": {
                "lag_3_to_5_rules": cycles["lag_3_to_5_rules"],
                "repeating_lead_pairs": cycles["repeating_lead_pairs"],
            },
        }


def grade_prediction(pred: Dict[str, object], actual: DrawRecord) -> Dict[str, object]:
    actual_set = {f"{n:02d}" for n in actual.numbers}
    rec_hits = [n for n in pred["recommended_numbers"] if n in actual_set]  # type: ignore[attr-defined]
    solo_list = [s["formatted"] for s in pred["solo_numbers"]]  # type: ignore[attr-defined]
    solo_hits = [n for n in solo_list if n in actual_set]
    tudi = pred["tudigong_number"]["formatted"]  # type: ignore[index]
    tudi_hit = tudi in actual_set

    all_hits = sorted(set(rec_hits + solo_hits + ([tudi] if tudi_hit else [])))
    categories = []
    if tudi_hit:
        categories.append("土地公牌")
    if solo_hits:
        categories.append(f"獨支({','.join(solo_hits)})")
    if rec_hits:
        categories.append(f"推薦{len(pred['recommended_numbers'])}碼({','.join(rec_hits)})")  # type: ignore[arg-type]

    return {
        "draw_date": actual.draw_date,
        "actual_numbers": [f"{n:02d}" for n in actual.numbers],
        "predicted_recommended": pred["recommended_numbers"],
        "predicted_solo": solo_list,
        "predicted_tudigong": tudi,
        "predicted_flames": pred.get("ai_flame_numbers", []),
        "tudigong_is_flame": bool(pred["tudigong_number"].get("is_flame", False)),
        "hit_numbers": all_hits,
        "hit_count": len(all_hits),
        "hit_categories": categories if categories else ["未命中"],
        "tudigong_hit": tudi_hit,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="今彩539 88期滾動分析＋冷門破冰＋AI火焰判定系統")
    parser.add_argument("--history-json", default="data/539_history.json")
    parser.add_argument("--pred-history-json", default="data/539_prediction_history.json")
    parser.add_argument("--out", default="output/539_latest_recommend.json")
    parser.add_argument("--update", action="store_true")
    parser.add_argument("--top", type=int, default=7, choices=[7])
    args = parser.parse_args()

    history_path = Path(args.history_json)
    records: List[DrawRecord] = []
    if history_path.exists():
        for item in json.loads(history_path.read_text(encoding="utf-8")):
            records.append(DrawRecord(item["draw_date"], item.get("period", ""), tuple(item["numbers"])))
    if args.update:
        for fetcher_name, fetcher in [("lotto-8", fetch_from_lotto8), ("pilio", fetch_from_pilio)]:
            try:
                fetched = fetcher()
                print(f"[{fetcher_name}] 取得 {len(fetched)} 期（最新：{fetched[-1].draw_date if fetched else '無'}）")
                records.extend(fetched)
            except Exception as exc:
                print(f"[{fetcher_name}] 抓取失敗略過：{exc}")
    records = filter_since_114(deduplicate_and_sort(records))
    if len(records) < 20:
        raise SystemExit("歷史資料不足。")

    history_path.parent.mkdir(parents=True, exist_ok=True)
    history_path.write_text(json.dumps([asdict(r) for r in records], ensure_ascii=False, indent=2), encoding="utf-8")

    pred_hist_path = Path(args.pred_history_json)
    pred_history: Dict[str, Dict[str, object]] = {}
    if pred_hist_path.exists():
        for item in json.loads(pred_hist_path.read_text(encoding="utf-8")):
            pred_history[item["draw_date"]] = item

    start_idx = max(88, len(records) - 20)
    for idx in range(start_idx, len(records)):
        actual = records[idx]
        if actual.draw_date not in pred_history:
            prior_pred = Rolling88Analyzer(records[:idx], window=88).generate_prediction(actual.draw_date, top_k=args.top)
            pred_history[actual.draw_date] = grade_prediction(prior_pred, actual)

    sorted_pred_history = [pred_history[d] for d in sorted(pred_history.keys(), reverse=True)]
    pred_hist_path.parent.mkdir(parents=True, exist_ok=True)
    pred_hist_path.write_text(json.dumps(sorted_pred_history, ensure_ascii=False, indent=2), encoding="utf-8")

    latest_date = dt.date.fromisoformat(records[-1].draw_date)
    next_date = latest_date + dt.timedelta(days=1)
    if next_date.weekday() == 6:
        next_date += dt.timedelta(days=1)

    next_pred = Rolling88Analyzer(records, window=88).generate_prediction(next_date.isoformat(), top_k=args.top)
    next_pred["recent_graded_history"] = sorted_pred_history[:30]

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(next_pred, ensure_ascii=False, indent=2), encoding="utf-8")

    print(f"下期 ({next_date}) 推薦 {args.top} 碼：{next_pred['recommended_numbers']}")
    print(f"AI火焰高機率：{next_pred['ai_flame_numbers']}")
    print(f"獨支：{[s['formatted'] for s in next_pred['solo_numbers']]}")
    print(f"土地公幸運號(已排除主牌與獨支)：{next_pred['tudigong_number']['formatted']}")
    print(f"88期最久未開Top5：{[(c['formatted'], c['omitted_draws']) for c in next_pred['cold_tracking']['cold_top5']]}")


if __name__ == "__main__":
    main()