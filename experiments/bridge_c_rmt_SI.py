#!/usr/bin/env python3
"""
Bridge C × RMT: Supplementary Analysis
========================================
additional verification for SI:
  1. Δ_left × Δ_right geometric mean vs |Z'|
  2. Height-corrected residual regression
  3. Softest tail left/right asymmetry
Requires: zeros6.txt (recomputes Z' for 2000 zeros, ~12 min)
"""

import mpmath as mp
import numpy as np
import matplotlib.pyplot as plt
from scipy import stats
import time

mp.mp.dps = 25

ZEROS_FILE = '/content/zeros6.txt'
N_SAMPLE = 2000
SEED = 42
OUTDIR = '/content/drive/MyDrive'

# ============================================================
# Load zeros
# ============================================================
print("="*70)
print("Bridge C × RMT: Supplementary Analysis (SI)")
print("="*70)

print("\nLoading zeros...")
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
print(f"  Loaded: {N_total} zeros")

# ============================================================
# Sample and compute Z'
# ============================================================
rng = np.random.RandomState(SEED)
valid_indices = np.arange(1, N_total - 1)
sample_idx = sorted(rng.choice(valid_indices, N_SAMPLE, replace=False))

def hardy_theta(t):
    t = mp.mpf(t)
    z = mp.mpc(mp.mpf("0.25"), t / 2)
    return mp.im(mp.loggamma(z)) - (t / 2) * mp.log(mp.pi)

def hardy_Z(t):
    t = mp.mpf(t)
    s = mp.mpc(mp.mpf("0.5"), t)
    return mp.re(mp.exp(1j * hardy_theta(t)) * mp.zeta(s))

def hardy_Z_prime(t):
    return mp.diff(hardy_Z, mp.mpf(t))

sample_data = []
for idx in sample_idx:
    sample_data.append({
        'gamma': all_zeros[idx],
        'delta_left': all_zeros[idx] - all_zeros[idx-1],
        'delta_right': all_zeros[idx+1] - all_zeros[idx],
    })

print(f"\nComputing Z'(γ) for {N_SAMPLE} zeros...")
t0 = time.time()
for i, d in enumerate(sample_data):
    zp = float(hardy_Z_prime(d['gamma']))
    d['Z_prime'] = zp
    d['abs_Z_prime'] = abs(zp)
    d['inv_abs_Z_prime'] = 1.0/abs(zp) if abs(zp) > 0 else np.nan
    d['delta_min'] = min(d['delta_left'], d['delta_right'])
    d['delta_geom'] = np.sqrt(d['delta_left'] * d['delta_right'])
    d['delta_prod'] = d['delta_left'] * d['delta_right']
    d['log_delta_sum'] = np.log(d['delta_left']) + np.log(d['delta_right'])
    if (i+1) % 500 == 0:
        elapsed = time.time() - t0
        print(f"  [{i+1}/{N_SAMPLE}] {elapsed:.0f}s")
print(f"  Done in {time.time()-t0:.0f}s")

# Arrays
gammas = np.array([d['gamma'] for d in sample_data])
abs_zp = np.array([d['abs_Z_prime'] for d in sample_data])
inv_zp = np.array([d['inv_abs_Z_prime'] for d in sample_data])
delta_min = np.array([d['delta_min'] for d in sample_data])
delta_left = np.array([d['delta_left'] for d in sample_data])
delta_right = np.array([d['delta_right'] for d in sample_data])
delta_geom = np.array([d['delta_geom'] for d in sample_data])
delta_prod = np.array([d['delta_prod'] for d in sample_data])
log_delta_sum = np.array([d['log_delta_sum'] for d in sample_data])

# ============================================================
# SI-1: Geometric mean Δ vs |Z'|
# ============================================================
print(f"\n{'='*60}")
print("SI-1: GEOMETRIC MEAN Δ vs |Z'|")
print(f"{'='*60}")

r_min, p_min = stats.spearmanr(delta_min, abs_zp)
r_geom, p_geom = stats.spearmanr(delta_geom, abs_zp)
r_prod, p_prod = stats.spearmanr(delta_prod, abs_zp)
r_logsum, p_logsum = stats.pearsonr(log_delta_sum, np.log(abs_zp))

print(f"  Δ_min vs |Z'|:                  Spearman r = {r_min:+.4f} (p={p_min:.2e})")
print(f"  √(Δ_L·Δ_R) vs |Z'|:            Spearman r = {r_geom:+.4f} (p={p_geom:.2e})")
print(f"  Δ_L·Δ_R vs |Z'|:               Spearman r = {r_prod:+.4f} (p={p_prod:.2e})")
print(f"  log Δ_L + log Δ_R vs log |Z'|:  Pearson  r = {r_logsum:+.4f} (p={p_logsum:.2e})")

print(f"\n  → Geometric mean {'STRONGER' if abs(r_geom) > abs(r_min) else 'WEAKER'} than Δ_min")
print(f"  → log sum {'STRONGER' if abs(r_logsum) > abs(r_min) else 'WEAKER'} than Δ_min")

# ============================================================
# SI-2: Residual regression (height correction)
# ============================================================
print(f"\n{'='*60}")
print("SI-2: RESIDUAL REGRESSION")
print(f"{'='*60}")

log_zp = np.log(abs_zp)
log_dmin = np.log(delta_min)
log_loggamma = np.log(np.log(gammas / (2*np.pi)))

# Model: log|Z'| = a·log Δ_min + b·log log γ + c
from numpy.linalg import lstsq
X = np.column_stack([log_dmin, log_loggamma, np.ones(len(gammas))])
coeffs, residuals, rank, sv = lstsq(X, log_zp, rcond=None)
a, b, c = coeffs

log_zp_pred = X @ coeffs
resid = log_zp - log_zp_pred

print(f"  log|Z'| = {a:.4f}·log Δ_min + {b:.4f}·log log(γ/2π) + {c:.4f}")
print(f"  R² = {1 - np.var(resid)/np.var(log_zp):.4f}")
print(f"  Residual std = {np.std(resid):.4f}")

# Partial correlation: spacing effect after removing height
r_partial_sp, p_partial_sp = stats.spearmanr(log_dmin, resid)
print(f"\n  Partial: log Δ_min vs residual: r = {r_partial_sp:+.4f} (p={p_partial_sp:.2e})")
print(f"  → Spacing effect {'SURVIVES' if p_partial_sp < 0.01 else 'DISAPPEARS'} after height correction")

# ============================================================
# SI-3: Softest tail left/right asymmetry
# ============================================================
print(f"\n{'='*60}")
print("SI-3: SOFTEST TAIL LEFT/RIGHT ASYMMETRY")
print(f"{'='*60}")

p99 = np.percentile(inv_zp, 99)
p95 = np.percentile(inv_zp, 95)
p1 = np.percentile(inv_zp, 1)
p5 = np.percentile(inv_zp, 5)

for label, mask in [("Top 1% (softest)", inv_zp >= p99),
                     ("Top 5% (soft)", inv_zp >= p95),
                     ("Bottom 1% (stiffest)", inv_zp <= p1),
                     ("Bottom 5% (stiff)", inv_zp <= p5)]:
    n = mask.sum()
    dl = delta_left[mask]
    dr = delta_right[mask]
    
    # Which side is closer?
    left_closer = (dl < dr).sum()
    right_closer = (dl > dr).sum()
    ratio = dl / dr
    
    print(f"\n  {label} (N={n}):")
    print(f"    median Δ_left  = {np.median(dl):.4f}")
    print(f"    median Δ_right = {np.median(dr):.4f}")
    print(f"    left closer: {left_closer}/{n} ({100*left_closer/n:.0f}%)")
    print(f"    right closer: {right_closer}/{n} ({100*right_closer/n:.0f}%)")
    print(f"    median Δ_L/Δ_R = {np.median(ratio):.4f}")
    
    if n >= 5:
        # Is one side systematically closer?
        t_stat, t_pval = stats.wilcoxon(dl - dr)
        print(f"    Wilcoxon signed-rank (L vs R): p = {t_pval:.4e}")
        if t_pval < 0.05:
            print(f"    → ASYMMETRIC: {'left' if np.median(dl) < np.median(dr) else 'right'} side is closer")
        else:
            print(f"    → SYMMETRIC: no preferred side")

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

# SI-1a: Δ_min vs |Z'| (reference)
ax = axes[0,0]
ax.scatter(np.log(delta_min), np.log(abs_zp), s=2, alpha=0.3, color='#00e5ff', rasterized=True)
slope_min, int_min, _, _, _ = stats.linregress(np.log(delta_min), np.log(abs_zp))
x_fit = np.linspace(np.log(delta_min).min(), np.log(delta_min).max(), 100)
ax.plot(x_fit, slope_min*x_fit + int_min, '--', color='#ff1744', lw=2)
ax.set_xlabel('log Δ_min'); ax.set_ylabel("log |Z'|")
ax.set_title(f'Δ_min: r={r_min:+.4f}, slope={slope_min:.3f}', fontweight='bold')
ax.grid(True, alpha=0.3)

# SI-1b: √(Δ_L·Δ_R) vs |Z'|
ax = axes[0,1]
ax.scatter(np.log(delta_geom), np.log(abs_zp), s=2, alpha=0.3, color='#76ff03', rasterized=True)
slope_g, int_g, _, _, _ = stats.linregress(np.log(delta_geom), np.log(abs_zp))
x_fit = np.linspace(np.log(delta_geom).min(), np.log(delta_geom).max(), 100)
ax.plot(x_fit, slope_g*x_fit + int_g, '--', color='#ff1744', lw=2)
ax.set_xlabel('log √(Δ_L·Δ_R)'); ax.set_ylabel("log |Z'|")
ax.set_title(f'Geom mean: r={r_geom:+.4f}, slope={slope_g:.3f}', fontweight='bold')
ax.grid(True, alpha=0.3)

# SI-1c: log Δ_L + log Δ_R vs log |Z'|
ax = axes[0,2]
ax.scatter(log_delta_sum, np.log(abs_zp), s=2, alpha=0.3, color='#ff6d00', rasterized=True)
slope_ls, int_ls, _, _, _ = stats.linregress(log_delta_sum, np.log(abs_zp))
x_fit = np.linspace(log_delta_sum.min(), log_delta_sum.max(), 100)
ax.plot(x_fit, slope_ls*x_fit + int_ls, '--', color='#ff1744', lw=2)
ax.set_xlabel('log Δ_L + log Δ_R'); ax.set_ylabel("log |Z'|")
ax.set_title(f'Log sum: Pearson r={r_logsum:+.4f}, slope={slope_ls:.3f}', fontweight='bold')
ax.grid(True, alpha=0.3)

# SI-2: Residual after height correction
ax = axes[1,0]
ax.scatter(log_dmin, resid, s=2, alpha=0.3, color='#e040fb', rasterized=True)
ax.axhline(0, color='#666', lw=1)
ax.set_xlabel('log Δ_min'); ax.set_ylabel('residual (height-corrected)')
ax.set_title(f'Partial: r={r_partial_sp:+.4f} (spacing after height removal)',
             fontweight='bold')
ax.grid(True, alpha=0.3)

# SI-3: Left/right asymmetry of softest zeros
ax = axes[1,1]
top5_mask = inv_zp >= p95
bot5_mask = inv_zp <= p5
ratio_top5 = delta_left[top5_mask] / delta_right[top5_mask]
ratio_bot5 = delta_left[bot5_mask] / delta_right[bot5_mask]

ax.hist(np.log2(ratio_top5), bins=30, alpha=0.6, color='#ff1744', density=True,
        label=f'Softest 5% (N={top5_mask.sum()})', edgecolor='none')
ax.hist(np.log2(ratio_bot5), bins=30, alpha=0.6, color='#76ff03', density=True,
        label=f'Stiffest 5% (N={bot5_mask.sum()})', edgecolor='none')
ax.axvline(0, color='#ffff00', ls='--', lw=2, label='symmetric (L=R)')
ax.set_xlabel('log₂(Δ_left / Δ_right)')
ax.set_ylabel('density')
ax.set_title('Left/Right Asymmetry\n(0 = symmetric)', fontweight='bold')
ax.legend(fontsize=9)
ax.grid(True, alpha=0.3)

# Summary
ax = axes[1,2]
ax.axis('off')
txt = f"""
SUPPLEMENTARY RESULTS
{'='*44}

SI-1: Spacing predictors of |Z'|
  Δ_min:              r = {r_min:+.4f}
  √(Δ_L·Δ_R):        r = {r_geom:+.4f}
  Δ_L·Δ_R:            r = {r_prod:+.4f}
  log Δ_L + log Δ_R:  r = {r_logsum:+.4f}

SI-2: Height-corrected regression
  log|Z'| = {a:.3f}·logΔ + {b:.3f}·loglogγ + {c:.3f}
  R² = {1 - np.var(resid)/np.var(log_zp):.4f}
  Partial r (spacing|height) = {r_partial_sp:+.4f}

SI-3: Softest tail L/R asymmetry
  → See histogram and Wilcoxon tests
"""
ax.text(0.05, 0.95, txt, transform=ax.transAxes, fontsize=11,
        fontfamily='monospace', color='#e0e0e0', va='top',
        bbox=dict(boxstyle='round', facecolor='#1a1a1a', alpha=0.9, pad=1))

plt.suptitle("Bridge C × RMT: Supplementary Analysis\n"
             "Geometric mean, height regression, L/R asymmetry",
             fontsize=14, fontweight='bold', color='#ffffff', y=1.02)
plt.tight_layout()
plt.savefig(f'{OUTDIR}/bridge_c_rmt_SI.png', dpi=150, bbox_inches='tight', facecolor='#0a0a0a')
plt.close()

# Save data
import pandas as pd
pd.DataFrame(sample_data).to_csv(f'{OUTDIR}/bridge_c_rmt_SI_data.csv', index=False)

print(f"\nSaved: {OUTDIR}/bridge_c_rmt_SI.png")
print(f"Saved: {OUTDIR}/bridge_c_rmt_SI_data.csv")
print(f"\n{'='*70}\nDONE\n{'='*70}")
