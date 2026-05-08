#!/usr/bin/env python3
"""
Bridge C × RMT: True Adjacent Spacing vs Stiffness
====================================================
Question: Does GUE level repulsion control Z'(γ_k)?

If Z'(γ_k) correlates with true adjacent spacing Δ_k,
then GUE zero statistics → Bridge C stiffness.

Strategy:
  1. Compute ALL adjacent spacings Δ_k from 2M zeros (instant)
  2. Sample ~2000 zeros
  3. Compute Z'(γ_k) for each sampled zero
  4. Correlate Δ_k vs |Z'(γ_k)|
"""

import mpmath as mp
import numpy as np
import matplotlib.pyplot as plt
from scipy import stats
import time

mp.mp.dps = 25

# ============================================================
# Config
# ============================================================
ZEROS_FILE = '/content/zeros6.txt'
N_SAMPLE = 2000  # zeros for Z' computation
SEED = 42
OUTDIR = '/content/drive/MyDrive'

# ============================================================
# Load ALL zeros and compute spacings
# ============================================================
print("="*70)
print("Bridge C × RMT: Adjacent Spacing vs Stiffness")
print("="*70)

print("\nLoading ALL zeros...")
t0 = time.time()
all_zeros = []
with open(ZEROS_FILE, 'r') as f:
    for line in f:
        line = line.strip()
        if line:
            try:
                all_zeros.append(float(line))
            except ValueError:
                continue

all_zeros = np.array(sorted(all_zeros))
N_total = len(all_zeros)
print(f"  Loaded: {N_total} zeros in {time.time()-t0:.1f}s")
print(f"  Range: [{all_zeros[0]:.2f}, {all_zeros[-1]:.2f}]")

# ALL adjacent spacings
all_spacings = np.diff(all_zeros)
print(f"\n  Adjacent spacings: N={len(all_spacings)}")
print(f"  mean Δ = {np.mean(all_spacings):.6f}")
print(f"  median Δ = {np.median(all_spacings):.6f}")
print(f"  min Δ = {np.min(all_spacings):.6f}")
print(f"  max Δ = {np.max(all_spacings):.6f}")

# ============================================================
# GUE spacing check (bonus)
# ============================================================
print(f"\n{'='*60}")
print("GUE CHECK: Normalized spacing distribution")
print(f"{'='*60}")

# Normalize spacings by local mean (unfolding)
# Use running mean with window
window = 50
local_means = np.convolve(all_spacings, np.ones(window)/window, mode='valid')
# Align: skip edges
start = window // 2
end = start + len(local_means)
normalized_spacings = all_spacings[start:end] / local_means

print(f"  Normalized spacings: N={len(normalized_spacings)}")
print(f"  mean = {np.mean(normalized_spacings):.4f} (should be ≈1)")
print(f"  std = {np.std(normalized_spacings):.4f}")

# Spacing ratio for GUE check
sr = []
for i in range(len(normalized_spacings) - 1):
    s1, s2 = normalized_spacings[i], normalized_spacings[i+1]
    if s1 > 0 and s2 > 0:
        sr.append(min(s1,s2)/max(s1,s2))
sr = np.array(sr)
R_POISSON = 2*np.log(2) - 1
R_GOE = 4 - 2*np.sqrt(3)
R_GUE = 2*np.sqrt(3)/np.pi - 0.5
r_mean_spacing = np.mean(sr)
print(f"\n  Zero SPACING ⟨r⟩ = {r_mean_spacing:.5f}")
print(f"    Poisson: {R_POISSON:.5f} (Δ={abs(r_mean_spacing-R_POISSON):.5f})")
print(f"    GOE:     {R_GOE:.5f} (Δ={abs(r_mean_spacing-R_GOE):.5f})")
print(f"    GUE:     {R_GUE:.5f} (Δ={abs(r_mean_spacing-R_GUE):.5f})")
best_sp = min([(abs(r_mean_spacing-R_POISSON),'Poisson'),
               (abs(r_mean_spacing-R_GOE),'GOE'),
               (abs(r_mean_spacing-R_GUE),'GUE')])
print(f"    → Best: {best_sp[1]} ✓ (Montgomery-Odlyzko confirmation)")

# ============================================================
# Sample zeros for Z' computation
# ============================================================
print(f"\n{'='*60}")
print(f"Sampling {N_SAMPLE} zeros for Z'(γ) computation")
print(f"{'='*60}")

rng = np.random.RandomState(SEED)
# Sample indices (not first/last to have both Δ_left and Δ_right)
valid_indices = np.arange(1, N_total - 1)
sample_idx = sorted(rng.choice(valid_indices, N_SAMPLE, replace=False))

# For each sampled zero, get:
#   γ_k, Δ_left = γ_k - γ_{k-1}, Δ_right = γ_{k+1} - γ_k, Δ_min = min(Δ_left, Δ_right)
sample_data = []
for idx in sample_idx:
    gamma = all_zeros[idx]
    delta_left = all_zeros[idx] - all_zeros[idx-1]
    delta_right = all_zeros[idx+1] - all_zeros[idx]
    delta_min = min(delta_left, delta_right)
    sample_data.append({
        'idx': idx,
        'gamma': gamma,
        'delta_left': delta_left,
        'delta_right': delta_right,
        'delta_min': delta_min,
    })

print(f"  Sampled {len(sample_data)} zeros")
print(f"  γ range: [{sample_data[0]['gamma']:.2f}, {sample_data[-1]['gamma']:.2f}]")
print(f"  median Δ_min: {np.median([d['delta_min'] for d in sample_data]):.6f}")

# ============================================================
# Compute Z'(γ_k) for sampled zeros
# ============================================================
print(f"\n{'='*60}")
print(f"Computing Z'(γ) for {N_SAMPLE} zeros...")
print(f"{'='*60}")

def hardy_theta(t):
    t = mp.mpf(t)
    z = mp.mpc(mp.mpf("0.25"), t / 2)
    return mp.im(mp.loggamma(z)) - (t / 2) * mp.log(mp.pi)

def hardy_Z(t):
    t = mp.mpf(t)
    s = mp.mpc(mp.mpf("0.5"), t)
    val = mp.exp(1j * hardy_theta(t)) * mp.zeta(s)
    return mp.re(val)

def hardy_Z_prime(t):
    return mp.diff(hardy_Z, mp.mpf(t))

t_start = time.time()
for i, d in enumerate(sample_data):
    zp = hardy_Z_prime(d['gamma'])
    d['Z_prime'] = float(zp)
    d['abs_Z_prime'] = abs(float(zp))
    d['inv_abs_Z_prime'] = 1.0/abs(float(zp)) if abs(float(zp)) > 0 else np.nan
    
    if (i+1) % 200 == 0:
        elapsed = time.time() - t_start
        rate = (i+1) / elapsed
        remaining = (len(sample_data) - i - 1) / rate
        print(f"  [{i+1}/{len(sample_data)}] {elapsed:.0f}s, ~{remaining:.0f}s left")

elapsed = time.time() - t_start
print(f"  Done in {elapsed:.0f}s")

# ============================================================
# CORE ANALYSIS: Δ_min vs |Z'(γ)|
# ============================================================
print(f"\n{'='*60}")
print("CORE: Adjacent spacing vs Z'(γ) correlation")
print(f"{'='*60}")

deltas = np.array([d['delta_min'] for d in sample_data])
abs_zp = np.array([d['abs_Z_prime'] for d in sample_data])
inv_zp = np.array([d['inv_abs_Z_prime'] for d in sample_data])
gammas = np.array([d['gamma'] for d in sample_data])

# Pearson and Spearman
r_pearson, p_pearson = stats.pearsonr(deltas, abs_zp)
r_spearman, p_spearman = stats.spearmanr(deltas, abs_zp)

print(f"\n  Δ_min vs |Z'(γ)|:")
print(f"    Pearson  r = {r_pearson:+.4f} (p = {p_pearson:.2e})")
print(f"    Spearman r = {r_spearman:+.4f} (p = {p_spearman:.2e})")

if p_spearman < 0.001:
    print(f"    *** SIGNIFICANT CORRELATION ***")
    if r_spearman > 0:
        print(f"    → Small spacing ↔ small |Z'| (shallow zero)")
        print(f"    → GUE repulsion → stiffness lower bound")
    else:
        print(f"    → Unexpected: negative correlation")
else:
    print(f"    → No significant correlation")

# Also: Δ_min vs 1/|Z'|
r_inv_p, p_inv_p = stats.pearsonr(deltas, inv_zp)
r_inv_s, p_inv_s = stats.spearmanr(deltas, inv_zp)
print(f"\n  Δ_min vs 1/|Z'(γ)| (inverse stiffness):")
print(f"    Pearson  r = {r_inv_p:+.4f} (p = {p_inv_p:.2e})")
print(f"    Spearman r = {r_inv_s:+.4f} (p = {p_inv_s:.2e})")

# Δ_left and Δ_right separately
delta_l = np.array([d['delta_left'] for d in sample_data])
delta_r = np.array([d['delta_right'] for d in sample_data])
r_l, p_l = stats.spearmanr(delta_l, abs_zp)
r_r, p_r = stats.spearmanr(delta_r, abs_zp)
print(f"\n  Δ_left vs |Z'|:  Spearman r = {r_l:+.4f} (p = {p_l:.2e})")
print(f"  Δ_right vs |Z'|: Spearman r = {r_r:+.4f} (p = {p_r:.2e})")

# ============================================================
# 無二 STEP: log-log correlation
# ============================================================
print(f"\n{'='*60}")
print("LOG-LOG CORRELATION (無二 requirement)")
print(f"{'='*60}")

log_delta = np.log(deltas)
log_abs_zp = np.log(abs_zp)
log_inv_zp = np.log(inv_zp[inv_zp > 0])

valid_log = np.isfinite(log_delta) & np.isfinite(log_abs_zp)
r_ll, p_ll = stats.spearmanr(log_delta[valid_log], log_abs_zp[valid_log])
print(f"  log Δ_min vs log |Z'|: Spearman r = {r_ll:+.4f} (p = {p_ll:.2e})")
r_ll_p, p_ll_p = stats.pearsonr(log_delta[valid_log], log_abs_zp[valid_log])
print(f"  log Δ_min vs log |Z'|: Pearson  r = {r_ll_p:+.4f} (p = {p_ll_p:.2e})")

valid_inv = np.isfinite(log_delta) & np.isfinite(np.log(inv_zp))
r_ll_inv, p_ll_inv = stats.spearmanr(log_delta[valid_inv], np.log(inv_zp[valid_inv]))
print(f"  log Δ_min vs log 1/|Z'|: Spearman r = {r_ll_inv:+.4f} (p = {p_ll_inv:.2e})")

# ============================================================
# 無二 STEP: Unfolded spacing (correct formula)
# ============================================================
print(f"\n{'='*60}")
print("UNFOLDED SPACING (Δ̄(γ) = 2π/log(γ/2π))")
print(f"{'='*60}")

delta_bar = 2 * np.pi / np.log(gammas / (2 * np.pi))
s_normalized = deltas / delta_bar

print(f"  mean s = {np.mean(s_normalized):.4f} (should be ≈ 1)")
print(f"  std s  = {np.std(s_normalized):.4f}")

r_unf, p_unf = stats.spearmanr(np.log(s_normalized), log_abs_zp[valid_log])
print(f"  log s vs log |Z'|: Spearman r = {r_unf:+.4f} (p = {p_unf:.2e})")

# ============================================================
# 無二 STEP: Tail condition
# ============================================================
print(f"\n{'='*60}")
print("TAIL CONDITION (top/bottom 1% of 1/|Z'|)")
print(f"{'='*60}")

p1 = np.percentile(inv_zp, 1)
p99 = np.percentile(inv_zp, 99)

bottom_1pct = inv_zp <= p1   # stiffest zeros (small 1/Z')
top_1pct = inv_zp >= p99     # softest zeros (large 1/Z')

delta_bottom = deltas[bottom_1pct]
delta_top = deltas[top_1pct]
s_bottom = s_normalized[bottom_1pct]
s_top = s_normalized[top_1pct]

print(f"  Bottom 1% of 1/|Z'| (stiffest, N={bottom_1pct.sum()}):")
print(f"    median Δ_min = {np.median(delta_bottom):.4f}")
print(f"    median s     = {np.median(s_bottom):.4f}")
print(f"  Top 1% of 1/|Z'| (softest, N={top_1pct.sum()}):")
print(f"    median Δ_min = {np.median(delta_top):.4f}")
print(f"    median s     = {np.median(s_top):.4f}")
print(f"  All zeros (N={len(deltas)}):")
print(f"    median Δ_min = {np.median(deltas):.4f}")
print(f"    median s     = {np.median(s_normalized):.4f}")

# Mann-Whitney U test: are top and bottom spacing distributions different?
u_stat, u_pval = stats.mannwhitneyu(delta_top, delta_bottom, alternative='less')
print(f"\n  Mann-Whitney U: top 1% spacing < bottom 1% spacing?")
print(f"    U = {u_stat:.0f}, p = {u_pval:.2e}")
if u_pval < 0.01:
    print(f"    *** CONFIRMED: softest zeros have smaller true spacings ***")
    print(f"    → GUE repulsion → stiffness lower bound → CONFIRMED")
else:
    print(f"    Not significant at p < 0.01")

# ============================================================
# Height-resolved analysis
# ============================================================
print(f"\n{'='*60}")
print("HEIGHT-RESOLVED: correlation in bins")
print(f"{'='*60}")

n_bins = 5
bin_edges = np.percentile(gammas, np.linspace(0, 100, n_bins+1))
for i in range(n_bins):
    mask = (gammas >= bin_edges[i]) & (gammas < bin_edges[i+1])
    if mask.sum() > 30:
        r_bin, p_bin = stats.spearmanr(deltas[mask], abs_zp[mask])
        print(f"  γ ∈ [{bin_edges[i]:.0f}, {bin_edges[i+1]:.0f}]: "
              f"N={mask.sum()}, Spearman r={r_bin:+.4f} (p={p_bin:.2e})")

# ============================================================
# FIGURE
# ============================================================
plt.rcParams.update({
    'font.size': 11,
    'figure.facecolor': '#0a0a0a',
    'axes.facecolor': '#111111',
    'text.color': '#e0e0e0',
    'axes.edgecolor': '#333333',
    'axes.labelcolor': '#cccccc',
    'xtick.color': '#999999',
    'ytick.color': '#999999',
    'grid.color': '#222222',
})

fig, axes = plt.subplots(2, 3, figsize=(20, 13))

# (0,0) Δ_min vs |Z'(γ)| — THE core plot
ax = axes[0, 0]
ax.scatter(deltas, abs_zp, s=3, alpha=0.4, color='#00e5ff', rasterized=True)
ax.set_xlabel('Δ_min (true adjacent spacing)')
ax.set_ylabel("|Z'(γ)| (stiffness)")
ax.set_title(f'Core: Spacing vs Stiffness\n'
             f'Spearman r={r_spearman:+.4f} (p={p_spearman:.2e})',
             fontweight='bold')
ax.set_yscale('log')
ax.grid(True, which='both', alpha=0.3)

# Running median
n_qbins = 15
qedges = np.percentile(deltas, np.linspace(0, 100, n_qbins+1))
med_x, med_y = [], []
for j in range(n_qbins):
    m = (deltas >= qedges[j]) & (deltas < qedges[j+1])
    if m.sum() > 5:
        med_x.append(np.median(deltas[m]))
        med_y.append(np.median(abs_zp[m]))
ax.plot(med_x, med_y, 'o-', color='#ff1744', lw=2, ms=6, label='running median', zorder=5)
ax.legend(fontsize=9)

# (0,1) Δ_min vs 1/|Z'(γ)| (inverse stiffness)
ax = axes[0, 1]
ax.scatter(deltas, inv_zp, s=3, alpha=0.4, color='#ff6d00', rasterized=True)
ax.set_xlabel('Δ_min (true adjacent spacing)')
ax.set_ylabel("1/|Z'(γ)| (inverse stiffness)")
ax.set_title(f'Spacing vs Inverse Stiffness\n'
             f'Spearman r={r_inv_s:+.4f} (p={p_inv_s:.2e})',
             fontweight='bold')
ax.set_yscale('log')
ax.grid(True, which='both', alpha=0.3)

# (0,2) Normalized spacing distribution (GUE check)
ax = axes[0, 2]
# Use a subset for histogram
ns_sub = normalized_spacings[::10]  # thin for speed
ax.hist(ns_sub, bins=80, density=True, alpha=0.7, color='#76ff03',
        edgecolor='#333', label=f'ζ zeros (N={len(ns_sub)})')

# GUE Wigner surmise P(s) = (32/π²)s² exp(-4s²/π)
s = np.linspace(0, 4, 300)
p_gue = (32/np.pi**2) * s**2 * np.exp(-4*s**2/np.pi)
p_poisson = np.exp(-s)
ax.plot(s, p_gue, '-', color='#e040fb', lw=2.5, label='GUE (β=2)')
ax.plot(s, p_poisson, '--', color='#ff1744', lw=2, label='Poisson')
ax.set_xlabel('s (normalized spacing)')
ax.set_ylabel('P(s)')
ax.set_title(f'Zero Spacing: GUE Confirmation\n⟨r⟩={r_mean_spacing:.4f}',
             fontweight='bold')
ax.legend(fontsize=9)
ax.set_xlim(0, 4)
ax.grid(True, alpha=0.3)

# (1,0) LOG-LOG scatter: log Δ vs log |Z'|
ax = axes[1, 0]
ax.scatter(log_delta[valid_log], log_abs_zp[valid_log], s=3, alpha=0.3, 
           color='#e040fb', rasterized=True)
ax.set_xlabel('log Δ_min')
ax.set_ylabel("log |Z'(γ)|")
ax.set_title(f'Log-Log: Spacing vs Stiffness\n'
             f'Spearman r={r_ll:+.4f} (p={p_ll:.2e})',
             fontweight='bold')
ax.grid(True, alpha=0.3)
# Fit line
if abs(r_ll) > 0.05:
    slope, intercept, _, _, _ = stats.linregress(log_delta[valid_log], log_abs_zp[valid_log])
    x_fit = np.linspace(log_delta[valid_log].min(), log_delta[valid_log].max(), 100)
    ax.plot(x_fit, slope*x_fit + intercept, '--', color='#ffff00', lw=2, 
            label=f'slope={slope:.3f}')
    ax.legend(fontsize=9)

# (1,1) Tail condition: spacing distribution for top/bottom 1%
ax = axes[1, 1]
ax.hist(s_bottom, bins=30, alpha=0.6, color='#76ff03', density=True,
        label=f'Stiffest 1% (N={bottom_1pct.sum()})', edgecolor='none')
ax.hist(s_top, bins=30, alpha=0.6, color='#ff1744', density=True,
        label=f'Softest 1% (N={top_1pct.sum()})', edgecolor='none')
ax.set_xlabel('normalized spacing s = Δ/Δ̄(γ)')
ax.set_ylabel('density')
ax.set_title(f'Tail Test: Spacing of Stiffest vs Softest\n'
             f'(M-W p={u_pval:.2e})', fontweight='bold')
ax.legend(fontsize=9)
ax.grid(True, alpha=0.3)

# (1,2) Summary
ax = axes[1, 2]
ax.axis('off')
summary = f"""
BRIDGE C × RMT: STIFFNESS-SOURCE HYPOTHESIS
{'='*48}

Zero spacing (N={N_total}):
  ⟨r⟩ = {r_mean_spacing:.5f}  →  {best_sp[1]}

RAW correlation (N={N_SAMPLE}):
  Δ vs |Z'|:   r = {r_spearman:+.4f} (p={p_spearman:.2e})
  Δ vs 1/|Z'|: r = {r_inv_s:+.4f} (p={p_inv_s:.2e})

LOG-LOG correlation:
  log Δ vs log |Z'|: r = {r_ll:+.4f} (p={p_ll:.2e})

UNFOLDED:
  log s vs log |Z'|: r = {r_unf:+.4f} (p={p_unf:.2e})

TAIL TEST (top vs bottom 1%):
  Softest median s  = {np.median(s_top):.4f}
  Stiffest median s = {np.median(s_bottom):.4f}
  Mann-Whitney p    = {u_pval:.2e}

{'─'*48}
{'GUE repulsion → stiffness lower bound CONFIRMED' if u_pval < 0.01 and r_spearman > 0 else 'Further investigation needed'}
"""
ax.text(0.05, 0.95, summary, transform=ax.transAxes, fontsize=10.5,
        fontfamily='monospace', color='#e0e0e0', va='top',
        bbox=dict(boxstyle='round', facecolor='#1a1a1a', alpha=0.9, pad=1))

plt.suptitle("Bridge C × RMT: Does GUE Level Repulsion Control Stiffness?\n"
             f"True adjacent spacing Δ_k vs Z'(γ_k) for {N_SAMPLE} zeros",
             fontsize=14, fontweight='bold', color='#ffffff', y=1.02)
plt.tight_layout()
outpath = f'{OUTDIR}/bridge_c_rmt_spacing_stiffness.png'
plt.savefig(outpath, dpi=150, bbox_inches='tight', facecolor='#0a0a0a')
plt.close()
print(f"\nSaved: {outpath}")

print(f"\n{'='*70}")
print("DONE")
print(f"{'='*70}")
