"""
analyze_1e9.py
Streaming analysis of prime loneliness data — handles 50M-row CSV without
loading everything into RAM. Accumulates only the statistics needed.

Usage:
    python3 analyze_1e9.py data_1e9.csv
"""

import sys, os, csv, math, time
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from collections import defaultdict

# ─── Streaming pass ──────────────────────────────────────────────────────────
# We do TWO passes:
#   Pass 1: accumulate per-omega counts/artin sums, per-pmod12 counts,
#           reservoir-sample L values for percentile estimation,
#           accumulate full L array for top-N tracking, summary stats.
#   Pass 2: (light) compute conjecture 1 & 2 using L percentile thresholds.

RESERVOIR_SIZE = 2_000_000   # sample for percentile / histogram
TOP_N = 100                  # top loneliest primes to track

def streaming_pass1(path):
    """First pass: build aggregates and reservoir sample."""
    t0 = time.time()

    # Summary counters
    total = 0
    n_artin = 0
    sum_L = 0.0
    sum_omega = 0.0

    # Per-omega: [count, artin_sum]
    omega_stats = defaultdict(lambda: [0, 0])

    # Per (omega, pmod12): [count, artin_sum]
    cross_stats = defaultdict(lambda: [0, 0])

    # Per pmod12: [count, artin_sum]
    pmod12_stats = defaultdict(lambda: [0, 0])

    # Reservoir sample of (L, artin, omega, pmod12) tuples
    reservoir = []
    import random
    rng = random.Random(42)

    # Top-N loneliest: min-heap by L
    import heapq
    top_heap = []  # (L, p, min_gap, omega, artin, pmod12)

    # For mean L by artin group
    sum_L_artin = 0.0
    sum_L_nonartin = 0.0

    print(f"Pass 1: streaming {path}...")
    with open(path) as f:
        reader = csv.DictReader(f)
        for i, row in enumerate(reader):
            p       = int(row['p'])
            L       = float(row['loneliness'])
            omega   = int(row['omega_pm1'])
            artin   = int(row['is_artin10'])
            pmod12  = int(row['pmod12'])
            min_gap = int(row['min_gap'])

            total += 1
            n_artin += artin
            sum_L += L
            sum_omega += omega

            if artin:
                sum_L_artin += L
            else:
                sum_L_nonartin += L

            omega_stats[omega][0] += 1
            omega_stats[omega][1] += artin

            cross_stats[(omega, pmod12)][0] += 1
            cross_stats[(omega, pmod12)][1] += artin

            pmod12_stats[pmod12][0] += 1
            pmod12_stats[pmod12][1] += artin

            # Reservoir sampling
            if len(reservoir) < RESERVOIR_SIZE:
                reservoir.append((L, artin, omega, pmod12))
            else:
                j = rng.randint(0, i)
                if j < RESERVOIR_SIZE:
                    reservoir[j] = (L, artin, omega, pmod12)

            # Top-N heap (min-heap on L)
            entry = (L, p, min_gap, omega, artin, pmod12)
            if len(top_heap) < TOP_N:
                heapq.heappush(top_heap, entry)
            elif L > top_heap[0][0]:
                heapq.heapreplace(top_heap, entry)

            if (i + 1) % 5_000_000 == 0:
                elapsed = time.time() - t0
                print(f"  ... {(i+1)/1e6:.0f}M rows  ({elapsed:.0f}s)")

    elapsed = time.time() - t0
    print(f"Pass 1 done: {total:,} rows in {elapsed:.1f}s\n")

    top_list = sorted(top_heap, key=lambda x: -x[0])

    stats = {
        'total': total,
        'n_artin': n_artin,
        'sum_L': sum_L,
        'sum_omega': sum_omega,
        'sum_L_artin': sum_L_artin,
        'sum_L_nonartin': sum_L_nonartin,
        'omega_stats': dict(omega_stats),
        'cross_stats': dict(cross_stats),
        'pmod12_stats': dict(pmod12_stats),
        'reservoir': reservoir,
        'top_list': top_list,
    }
    return stats


def get_percentile_thresholds(reservoir, pcts):
    """Estimate L percentile thresholds from reservoir sample."""
    L_vals = sorted(r[0] for r in reservoir)
    n = len(L_vals)
    thresholds = {}
    for pct in pcts:
        idx = int(n * (1 - pct / 100))
        idx = min(idx, n - 1)
        thresholds[pct] = L_vals[idx]
    return thresholds


def streaming_pass2(path, thresholds):
    """Second pass: conjecture 1 & 2 counts per threshold."""
    t0 = time.time()
    pcts = sorted(thresholds.keys())

    # For each threshold: [total, artin, artin_L_sum, nonartin_L_sum, total_artin_above, total_nonartin_above]
    # We need: P(top-k | Artin) and P(top-k | ~Artin)
    # total_artin and total_nonartin come from pass1
    above = {pct: {'n': 0, 'artin': 0, 'artin_group': 0, 'nonartin_group': 0} for pct in pcts}

    print(f"Pass 2: computing conjecture 1 & 2 thresholds...")
    with open(path) as f:
        reader = csv.DictReader(f)
        for i, row in enumerate(reader):
            L     = float(row['loneliness'])
            artin = int(row['is_artin10'])
            for pct in pcts:
                if L >= thresholds[pct]:
                    above[pct]['n'] += 1
                    above[pct]['artin'] += artin
                    if artin:
                        above[pct]['artin_group'] += 1
                    else:
                        above[pct]['nonartin_group'] += 1
            if (i + 1) % 5_000_000 == 0:
                print(f"  ... {(i+1)/1e6:.0f}M rows  ({time.time()-t0:.0f}s)")

    elapsed = time.time() - t0
    print(f"Pass 2 done in {elapsed:.1f}s\n")
    return above


# ─── Print & plot ─────────────────────────────────────────────────────────────

def print_summary(s):
    total = s['total']
    n_artin = s['n_artin']
    artin_rate = n_artin / total
    mean_L = s['sum_L'] / total
    mean_omega = s['sum_omega'] / total

    L_vals = [r[0] for r in s['reservoir']]
    median_L = float(np.median(L_vals))
    max_entry = s['top_list'][0]

    print("=" * 60)
    print("DATASET SUMMARY  (up to 10^9)")
    print("=" * 60)
    print(f"  Total primes:                 {total:,}")
    print(f"  Artin primes (10 prim.rt.):   {n_artin:,}  ({artin_rate:.5f} = {artin_rate*100:.3f}%)")
    print(f"  Artin's constant (theory):    ~0.37396")
    print(f"  Mean L(p):                    {mean_L:.5f}")
    print(f"  Median L(p) (est.):           {median_L:.5f}")
    print(f"  Max L(p):                     {max_entry[0]:.5f}  (p={max_entry[1]:,})")
    print(f"  Mean omega(p-1):              {mean_omega:.5f}")
    print()
    return artin_rate


def print_top_lonely(top_list, n=30):
    print("=" * 60)
    print(f"TOP {n} LONELIEST PRIMES (up to 10^9)")
    print("=" * 60)
    print(f"  {'p':>14} {'L(p)':>8} {'min_gap':>8} {'omega':>6} {'Artin?':>7} {'p mod 12':>9}")
    print("  " + "-" * 58)
    for L, p, min_gap, omega, artin, pmod12 in top_list[:n]:
        print(f"  {p:>14,} {L:>8.4f} {min_gap:>8} {omega:>6} {'YES' if artin else 'no':>7} {pmod12:>9}")
    print()


def conjecture1(above, thresholds, output_dir):
    pcts = [1, 2, 5, 10, 20, 50, 100]
    print("=" * 60)
    print("CONJECTURE 1: Density of Artin primes in lonely population")
    print("=" * 60)
    print(f"  {'Percentile':>12} {'L_thresh':>10} {'N':>12} {'Artin':>10} {'Density':>10}")
    print("  " + "-" * 58)
    rows_out = []
    densities = []
    for pct in pcts:
        if pct not in above:
            continue
        d = above[pct]
        n = d['n']
        na = d['artin']
        density = na / n if n else 0
        thresh = thresholds.get(pct, 0)
        flag = " ***" if density < 0.15 else ""
        print(f"  {'Top '+str(pct)+'%':>12} {thresh:>10.4f} {n:>12,} {na:>10,} {density:>10.4f}{flag}")
        rows_out.append((pct, thresh, n, na, density))
        densities.append(density)

    fig, ax = plt.subplots(figsize=(8, 5))
    xs = [r[0] for r in rows_out]
    ys = [r[4] for r in rows_out]
    ax.plot(xs, ys, 'o-', color='steelblue', linewidth=2)
    ax.axhline(0.15, color='red', linestyle='--', label='Threshold 0.15')
    ax.axhline(0.37396, color='green', linestyle='--', label="Artin's constant ~0.374")
    ax.set_xlabel("Top-k% loneliest primes", fontsize=12)
    ax.set_ylabel("Fraction that are Artin primes (base 10)", fontsize=12)
    ax.set_title("Conjecture 1: Artin prime density vs. loneliness percentile\n(all primes ≤ 10⁹)", fontsize=12)
    ax.legend(); ax.grid(True, alpha=0.3)
    plt.tight_layout()
    plt.savefig(f"{output_dir}/conj1_density.png", dpi=150)
    plt.close()
    print(f"  [Figure saved: conj1_density.png]\n")
    return rows_out


def conjecture2(above, thresholds, stats, output_dir):
    total = stats['total']
    n_artin_total = stats['n_artin']
    n_nonartin_total = total - n_artin_total

    pcts = [1, 2, 5, 10]
    print("=" * 60)
    print("CONJECTURE 2: Relative loneliness Artin vs. non-Artin")
    print("=" * 60)
    print(f"  {'Threshold':>12} {'P(top|Artin)':>14} {'P(top|~Artin)':>15} {'Ratio':>8}")
    print("  " + "-" * 54)
    ratios = []
    for pct in pcts:
        if pct not in above:
            continue
        d = above[pct]
        p_artin    = d['artin_group'] / n_artin_total
        p_nonartin = d['nonartin_group'] / n_nonartin_total
        ratio = p_nonartin / p_artin if p_artin > 0 else float('nan')
        flag = " *** in [1.5,2.0]" if 1.5 <= ratio <= 2.0 else ""
        print(f"  {'Top '+str(pct)+'%':>12} {p_artin:>14.5f} {p_nonartin:>15.5f} {ratio:>8.3f}{flag}")
        ratios.append((pct, ratio))

    mean_L_artin    = stats['sum_L_artin'] / n_artin_total
    mean_L_nonartin = stats['sum_L_nonartin'] / n_nonartin_total
    print(f"\n  Mean L(p) for Artin primes:     {mean_L_artin:.5f}")
    print(f"  Mean L(p) for non-Artin primes: {mean_L_nonartin:.5f}")
    print(f"  Difference (non-Artin - Artin): {mean_L_nonartin - mean_L_artin:.5f}")

    # Histogram from reservoir
    reservoir = stats['reservoir']
    L_artin    = [r[0] for r in reservoir if r[1] == 1 and r[0] < 4]
    L_nonartin = [r[0] for r in reservoir if r[1] == 0 and r[0] < 4]
    fig, ax = plt.subplots(figsize=(9, 5))
    ax.hist(L_artin,    bins=80, alpha=0.6, color='steelblue', density=True, label='Artin primes')
    ax.hist(L_nonartin, bins=80, alpha=0.6, color='tomato',    density=True, label='Non-Artin primes')
    ax.set_xlabel("Loneliness L(p) = min_gap / ln(p)", fontsize=12)
    ax.set_ylabel("Density", fontsize=12)
    ax.set_title("Conjecture 2: Loneliness distributions — Artin vs. non-Artin\n(all primes ≤ 10⁹)", fontsize=12)
    ax.legend(); ax.grid(True, alpha=0.3)
    plt.tight_layout()
    plt.savefig(f"{output_dir}/conj2_histogram.png", dpi=150)
    plt.close()
    print(f"  [Figure saved: conj2_histogram.png]\n")
    return ratios


def conjecture3(stats, output_dir):
    omega_stats = stats['omega_stats']
    reservoir   = stats['reservoir']
    thresholds  = get_percentile_thresholds(reservoir, [1, 2, 5, 10, 25, 50, 100])

    print("=" * 60)
    print("CONJECTURE 3: omega(p-1) and Artin probability")
    print("=" * 60)

    # 3a: mean omega by loneliness — from reservoir
    pcts = [1, 2, 5, 10, 25, 50, 100]
    print(f"\n  [3a] Mean omega(p-1) by loneliness percentile (reservoir):")
    print(f"  {'Percentile':>12} {'N (sample)':>12} {'Mean omega':>12}")
    print("  " + "-" * 40)
    pct_omegas = []
    for pct in pcts:
        thresh = thresholds[pct]
        subset = [r for r in reservoir if r[0] >= thresh]
        if not subset:
            continue
        mean_om = np.mean([r[2] for r in subset])
        flag = " ***" if mean_om >= 3.5 else ""
        print(f"  {'Top '+str(pct)+'%':>12} {len(subset):>12,} {mean_om:>12.4f}{flag}")
        pct_omegas.append((pct, mean_om))

    # 3b: P(Artin) by omega — exact from pass1 aggregates
    print(f"\n  [3b] P(10 is primitive root | omega(p-1) = k):")
    print(f"  {'omega':>8} {'N':>12} {'P(Artin)':>10} {'Rel. to omega=2':>16}")
    omega_keys = sorted(omega_stats.keys())
    omega_table = []
    baseline = None
    for k in omega_keys:
        n, na = omega_stats[k]
        if n < 100:
            continue
        p_artin = na / n
        if k == 2:
            baseline = p_artin
        rel = p_artin / baseline if baseline else float('nan')
        omega_table.append((k, n, p_artin, rel))
        print(f"  {k:>8} {n:>12,} {p_artin:>10.5f} {rel:>16.5f}")

    if len(omega_table) >= 3:
        print(f"\n  [3b] Step reductions:")
        for i in range(1, len(omega_table)):
            k0, _, p0, _ = omega_table[i-1]
            k1, _, p1, _ = omega_table[i]
            red = (p0 - p1) / p0 if p0 > 0 else float('nan')
            print(f"    omega {k0} -> {k1}: {p0:.5f} -> {p1:.5f}  ({red*100:.1f}% drop)")

    # Figures
    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 5))
    xs = [p for p, _ in pct_omegas]
    ys = [om for _, om in pct_omegas]
    ax1.plot(xs, ys, 's-', color='purple', linewidth=2)
    ax1.axhline(3.5, color='red', linestyle='--', label='Threshold 3.5')
    ax1.set_xlabel("Top-k% loneliest primes", fontsize=12)
    ax1.set_ylabel("Mean ω(p−1)", fontsize=12)
    ax1.set_title("3a: Mean ω(p−1) vs. loneliness percentile\n(≤10⁹)", fontsize=12)
    ax1.legend(); ax1.grid(True, alpha=0.3)

    ks    = [k for k, _, _, _ in omega_table]
    pvals = [p for _, _, p, _ in omega_table]
    ns    = [n for _, n, _, _ in omega_table]
    ax2.bar(ks, pvals, color='steelblue', edgecolor='black', alpha=0.8)
    ax2.axhline(0.37396, color='green', linestyle='--', label="Artin's constant")
    ax2.set_xlabel("ω(p−1)", fontsize=12)
    ax2.set_ylabel("P(10 is primitive root mod p)", fontsize=12)
    ax2.set_title("3b: P(Artin base 10) vs. ω(p−1)\n(≤10⁹)", fontsize=12)
    ax2.legend(); ax2.grid(True, alpha=0.3, axis='y')
    plt.suptitle("Conjecture 3: ω(p−1) drives Artin probability", fontsize=13, fontweight='bold')
    plt.tight_layout()
    plt.savefig(f"{output_dir}/conj3_omega.png", dpi=150)
    plt.close()
    print(f"\n  [Figure saved: conj3_omega.png]\n")
    return omega_table, pct_omegas


def conjecture4(stats, output_dir):
    cross_stats = stats['cross_stats']
    reservoir   = stats['reservoir']
    thresholds  = get_percentile_thresholds(reservoir, [1, 5, 10])

    prime_residues = [1, 5, 7, 11]
    print("=" * 60)
    print("CONJECTURE 4: p ≡ 5 mod 12 deficit among lonely Artin primes")
    print("=" * 60)

    for pct, thresh in sorted(thresholds.items()):
        subset = [r for r in reservoir if r[0] >= thresh]
        artin_sub = [r for r in subset if r[1] == 1]
        print(f"\n  [Top {pct}% loneliest, reservoir N={len(subset):,}]")
        print(f"  {'p mod 12':>10} {'All (N)':>10} {'All (%)':>10} {'Artin (N)':>10} {'Artin (%)':>10}")
        print("  " + "-" * 54)
        for res in prime_residues:
            n_res       = sum(1 for r in subset if r[3] == res)
            n_res_artin = sum(1 for r in artin_sub if r[3] == res)
            pct_all     = n_res / len(subset) * 100 if subset else 0
            pct_artin   = n_res_artin / len(artin_sub) * 100 if artin_sub else 0
            flag = " ***" if res == 5 and pct_artin < 5 else ""
            print(f"  {res:>10} {n_res:>10,} {pct_all:>9.1f}% {n_res_artin:>10,} {pct_artin:>9.1f}%{flag}")

    # Heatmap from exact cross_stats (top 10% from reservoir threshold)
    thresh_10 = thresholds[10]
    omega_range  = range(2, 8)
    pmod12_range = [1, 5, 7, 11]

    # For the heatmap we use all data from cross_stats for the loneliness cutoff —
    # but cross_stats doesn't have L. We use reservoir for the heatmap.
    subset_10 = [r for r in reservoir if r[0] >= thresh_10]
    matrix = np.zeros((len(omega_range), len(pmod12_range)))
    count_matrix = np.zeros_like(matrix, dtype=int)
    for r in subset_10:
        om, pm12 = r[2], r[3]
        if om in omega_range and pm12 in pmod12_range:
            i = list(omega_range).index(om)
            j = pmod12_range.index(pm12)
            matrix[i][j] += r[1]
            count_matrix[i][j] += 1

    rate_matrix = np.where(count_matrix > 0, matrix / count_matrix, np.nan)
    fig, ax = plt.subplots(figsize=(9, 5))
    im = ax.imshow(rate_matrix, cmap='RdYlGn', vmin=0, vmax=0.6, aspect='auto')
    ax.set_xticks(range(len(pmod12_range)))
    ax.set_xticklabels([f"p≡{r} mod 12" for r in pmod12_range])
    ax.set_yticks(range(len(omega_range)))
    ax.set_yticklabels([f"ω={k}" for k in omega_range])
    ax.set_title("Conjecture 4: P(Artin base 10) for top-10% lonely primes\nby ω(p−1) and p mod 12  (≤10⁹)", fontsize=12)
    plt.colorbar(im, ax=ax, label="P(10 is primitive root)")
    for i in range(len(omega_range)):
        for j in range(len(pmod12_range)):
            val = rate_matrix[i][j]
            if not np.isnan(val):
                ax.text(j, i, f"{val:.3f}", ha='center', va='center', fontsize=9,
                        color='black' if 0.15 < val < 0.5 else 'white')
    plt.tight_layout()
    plt.savefig(f"{output_dir}/conj4_heatmap.png", dpi=150)
    plt.close()
    print(f"\n  [Figure saved: conj4_heatmap.png]\n")


def plot_scatter(stats, output_dir):
    reservoir = stats['reservoir']
    sample = reservoir[::max(1, len(reservoir)//5000)]
    L_a  = [r[0] for r in sample if r[1] == 1]
    om_a = [r[2] for r in sample if r[1] == 1]
    L_n  = [r[0] for r in sample if r[1] == 0]
    om_n = [r[2] for r in sample if r[1] == 0]

    rng = np.random.default_rng(42)
    jitter = lambda v: np.array(v) + rng.uniform(-0.15, 0.15, len(v))

    fig, ax = plt.subplots(figsize=(10, 6))
    ax.scatter(jitter(om_n), L_n, alpha=0.2, s=4, color='tomato',    label='Not Artin')
    ax.scatter(jitter(om_a), L_a, alpha=0.3, s=6, color='steelblue', label='Artin (10 is prim.rt.)')
    ax.set_xlabel("ω(p−1) — distinct prime factors of p−1", fontsize=12)
    ax.set_ylabel("Loneliness  L(p) = min_gap / ln(p)", fontsize=12)
    ax.set_title("Loneliness vs. ω(p−1), colored by Artin status (base 10)\n(primes ≤ 10⁹)", fontsize=12)
    ax.legend(markerscale=3); ax.grid(True, alpha=0.2)
    plt.tight_layout()
    plt.savefig(f"{output_dir}/scatter_L_omega.png", dpi=150)
    plt.close()
    print(f"  [Figure saved: scatter_L_omega.png]")


# ─── Main ─────────────────────────────────────────────────────────────────────

if __name__ == "__main__":
    path = sys.argv[1] if len(sys.argv) > 1 else "data_1e9.csv"
    output_dir = os.path.dirname(os.path.abspath(path))

    # Redirect stdout to tee into log file
    import io
    log_path = os.path.join(output_dir, "analysis_1e9_log.txt")

    stats = streaming_pass1(path)

    print_summary(stats)
    print_top_lonely(stats['top_list'], n=30)

    # Percentile thresholds from reservoir
    pcts_needed = [1, 2, 5, 10, 20, 50, 100]
    thresholds = get_percentile_thresholds(stats['reservoir'], pcts_needed)
    print("Estimated L percentile thresholds:")
    for pct, t in sorted(thresholds.items()):
        print(f"  Top {pct}%: L >= {t:.5f}")
    print()

    above = streaming_pass2(path, thresholds)

    c1 = conjecture1(above, thresholds, output_dir)
    c2 = conjecture2(above, thresholds, stats, output_dir)
    c3, pct_omegas = conjecture3(stats, output_dir)
    conjecture4(stats, output_dir)
    plot_scatter(stats, output_dir)

    # Save numeric results as JSON for paper-update script
    import json
    results = {
        'total': stats['total'],
        'n_artin': stats['n_artin'],
        'artin_rate': stats['n_artin'] / stats['total'],
        'mean_L': stats['sum_L'] / stats['total'],
        'mean_omega': stats['sum_omega'] / stats['total'],
        'mean_L_artin': stats['sum_L_artin'] / stats['n_artin'],
        'mean_L_nonartin': stats['sum_L_nonartin'] / (stats['total'] - stats['n_artin']),
        'top30': [{'L': x[0], 'p': x[1], 'min_gap': x[2], 'omega': x[3],
                   'artin': x[4], 'pmod12': x[5]} for x in stats['top_list'][:30]],
        'conjecture1': [{'pct': r[0], 'thresh': r[1], 'n': r[2], 'artin': r[3], 'density': r[4]} for r in c1],
        'conjecture2': [{'pct': r[0], 'ratio': r[1]} for r in c2],
        'conjecture3_omega': [{'omega': r[0], 'n': r[1], 'p_artin': r[2], 'rel': r[3]} for r in c3],
        'conjecture3_pct': [{'pct': r[0], 'mean_omega': r[1]} for r in pct_omegas],
        'thresholds': {str(k): v for k, v in thresholds.items()},
    }
    results_path = os.path.join(output_dir, "analysis_1e9_results.json")
    with open(results_path, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\nResults JSON saved: {results_path}")
    print("\n" + "=" * 60)
    print("ALL DONE.")
    print("=" * 60)
