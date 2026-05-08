#!/usr/bin/env python3
"""
Phase 2 Colab: Bridge C Response Operator — Large Scale
=========================================================
Colab version: reads /content/zeros6.txt (up to 2M zeros),
random-samples 100000, tracks per-zero response C_k.

Usage on Colab:
  1. Upload zeros6.txt to /content/
  2. pip install mpmath
  3. Run this script
"""

import mpmath as mp
import numpy as np
import matplotlib.pyplot as plt
import pandas as pd
from math import gcd
import time
import os

mp.mp.dps = 20  # 20 digits: fast + sufficient for zero tracking

# ============================================================
# Config
# ============================================================

ZEROS_FILE = '/content/zeros6.txt'
N_SAMPLE = 100000        # random sample size
EPS_VALUES = [1e-5, 1e-4, 1e-3]  # ε sweep for stability check
EPS_PRIMARY = 1e-4     # primary ε for detailed analysis
N_PERT = 400           # Dirichlet series truncation
SEED = 42              # reproducibility

# ============================================================
# Load zeros
# ============================================================

def load_zeros(path, n_sample=N_SAMPLE, seed=SEED):
    """Load zeros from file, random sample n_sample."""
    print(f"Loading zeros from {path}...")

    zeros = []
    with open(path, 'r') as f:
        for line in f:
            line = line.strip()
            if line:
                try:
                    zeros.append(float(line))
                except ValueError:
                    continue

    print(f"  Total zeros loaded: {len(zeros)}")

    # Sort
    zeros = sorted(zeros)

    # Random sample
    rng = np.random.RandomState(seed)
    if len(zeros) > n_sample:
        indices = sorted(rng.choice(len(zeros), n_sample, replace=False))
        sampled = [zeros[i] for i in indices]
    else:
        sampled = zeros

    print(f"  Sampled: {len(sampled)} zeros")
    print(f"  Range: [{sampled[0]:.2f}, {sampled[-1]:.2f}]")

    return sampled, zeros

# ============================================================
# Perturbation model (same as Phase 1b)
# ============================================================

def P8(x):
    return 256*x**4 - 512*x**3 + 3200*x**2 - 2944*x + 1680

# Precompute g8
_g8_cache = {}
_g8_max = None

def _init_g8(n_pert=N_PERT):
    global _g8_max
    raw = {}
    for n in range(2, n_pert + 1):
        raw[n] = float(P8(mp.log(n)))
    _g8_max = max(abs(v) for v in raw.values())
    for n in range(2, n_pert + 1):
        _g8_cache[n] = mp.mpf(raw[n]) / mp.mpf(_g8_max)

_init_g8()

def g8(n):
    return _g8_cache.get(n, mp.mpf(0))

def a_coeff(n, eps):
    return 1 + mp.mpf(eps) * g8(n)

# ============================================================
# Z_eps (coefficient perturbation, breaks Who + Where)
# ============================================================

def Z_eps(s, eps, n_pert=N_PERT):
    eps_mp = mp.mpf(eps)
    delta_eta = mp.mpc(0)
    for n in range(2, n_pert + 1):
        sign = 1 if (n % 2 == 1) else -1
        delta_eta += sign * eps_mp * g8(n) * mp.power(mp.mpf(n), -s)
    denom = 1 - mp.power(2, 1 - s)
    return mp.zeta(s) + delta_eta / denom

# ============================================================
# D_logadd
# ============================================================

def compute_D_logadd(eps, nmax=50):
    vals = []
    for m in range(2, nmax + 1):
        for n in range(2, nmax + 1):
            mn = m * n
            if mn <= nmax and gcd(m, n) == 1:
                a_mn = a_coeff(mn, eps)
                a_m = a_coeff(m, eps)
                a_n = a_coeff(n, eps)
                if a_mn > 0 and a_m > 0 and a_n > 0:
                    defect = float(abs(
                        mp.log(a_mn) - mp.log(a_m) - mp.log(a_n)
                    ))
                    vals.append(defect)
    return np.mean(vals) if vals else 0.0

# ============================================================
# Zero tracking
# ============================================================

def track_zero(eps, t0, timeout_s=10):
    """Track zero near (0.5, t0). Returns (Re, Im) or (nan, nan)."""
    def F(sigma, t):
        s = mp.mpc(sigma, t)
        z = Z_eps(s, eps)
        return (mp.re(z), mp.im(z))

    try:
        sigma, t = mp.findroot(F, (mp.mpf(0.5), mp.mpf(t0)),
                                tol=mp.mpf("1e-10"),
                                maxsteps=60)
        return float(mp.re(sigma)), float(mp.re(t))
    except:
        return float('nan'), float('nan')

# ============================================================
# Main scan
# ============================================================

def run_scan(zeros_sampled, eps_val=EPS_PRIMARY):
    """Single ε, all sampled zeros."""
    dla = compute_D_logadd(eps_val)

    print(f"\nε = {eps_val:.2e}")
    print(f"D_logadd = {dla:.6e}")
    print(f"Tracking {len(zeros_sampled)} zeros...")

    records = []
    t_start = time.time()

    for i, t0 in enumerate(zeros_sampled):
        sig, t = track_zero(eps_val, t0)

        delta_Re = sig - 0.5 if not np.isnan(sig) else np.nan
        delta_Im = t - t0 if not np.isnan(t) else np.nan
        Ck_Re = delta_Re / dla if dla > 0 and not np.isnan(delta_Re) else np.nan
        Ck_Im = delta_Im / dla if dla > 0 and not np.isnan(delta_Im) else np.nan

        records.append({
            'k': i + 1,
            'Im_rho_0': t0,
            'Re_eps': sig,
            'Im_eps': t,
            'delta_Re': delta_Re,
            'delta_Im': delta_Im,
            'Ck_Re': Ck_Re,
            'Ck_Im': Ck_Im,
        })

        if (i + 1) % 50 == 0:
            elapsed = time.time() - t_start
            rate = (i + 1) / elapsed
            remaining = (len(zeros_sampled) - i - 1) / rate
            n_ok = sum(1 for r in records if not np.isnan(r['Ck_Re']))
            print(f"  [{i+1}/{len(zeros_sampled)}] "
                  f"{elapsed:.0f}s elapsed, ~{remaining:.0f}s remaining, "
                  f"{n_ok} converged")

    elapsed = time.time() - t_start
    print(f"\nDone in {elapsed:.1f}s")

    df = pd.DataFrame(records)
    n_ok = df['Ck_Re'].notna().sum()
    print(f"Converged: {n_ok}/{len(zeros_sampled)}")

    return df, dla

def run_stability_check(zeros_sampled, eps_values=EPS_VALUES):
    """Multi-ε check on subset of zeros."""
    # Use first 100 for stability check
    subset = zeros_sampled[:min(10000, len(zeros_sampled))]

    all_records = []

    for eps in eps_values:
        dla = compute_D_logadd(eps)
        print(f"\nStability check: ε = {eps:.2e}, D_logadd = {dla:.6e}")

        for i, t0 in enumerate(subset):
            sig, t = track_zero(eps, t0)
            delta_Re = sig - 0.5 if not np.isnan(sig) else np.nan
            delta_Im = t - t0 if not np.isnan(t) else np.nan
            Ck_Re = delta_Re / dla if dla > 0 and not np.isnan(delta_Re) else np.nan
            Ck_Im = delta_Im / dla if dla > 0 and not np.isnan(delta_Im) else np.nan

            all_records.append({
                'epsilon': eps,
                'k': i + 1,
                'Im_rho_0': t0,
                'Ck_Re': Ck_Re,
                'Ck_Im': Ck_Im,
            })

        print(f"  Done ({len(subset)} zeros)")

    return pd.DataFrame(all_records)

# ============================================================
# Plotting
# ============================================================

def plot_all(df, dla, eps, outdir='/content/drive/MyDrive'):
    df_ok = df.dropna(subset=['Ck_Re', 'Ck_Im']).copy()

    fig, axes = plt.subplots(2, 2, figsize=(16, 12))

    # (0,0) C_k^Re vs Im(ρ)
    ax = axes[0, 0]
    ax.scatter(df_ok['Im_rho_0'], df_ok['Ck_Re'], s=3, alpha=0.5, color='#FF5722')
    ax.axhline(0, color='gray', linestyle='-', alpha=0.3)
    ax.set_xlabel('Im(ρ_k)', fontsize=12)
    ax.set_ylabel('C_k^Re', fontsize=12)
    ax.set_title(f'Bridge C: Re response per zero (ε={eps:.0e})', fontsize=13)
    ax.grid(True, alpha=0.3)

    # (0,1) C_k^Im vs Im(ρ)
    ax = axes[0, 1]
    ax.scatter(df_ok['Im_rho_0'], df_ok['Ck_Im'], s=3, alpha=0.5, color='#2196F3')
    ax.axhline(0, color='gray', linestyle='-', alpha=0.3)
    ax.set_xlabel('Im(ρ_k)', fontsize=12)
    ax.set_ylabel('C_k^Im', fontsize=12)
    ax.set_title(f'Bridge C: Im response per zero (ε={eps:.0e})', fontsize=13)
    ax.grid(True, alpha=0.3)

    # (1,0) |C_k^Re| envelope with running mean
    ax = axes[1, 0]
    abs_Ck_Re = np.abs(df_ok['Ck_Re'].values)
    im_vals = df_ok['Im_rho_0'].values
    ax.scatter(im_vals, abs_Ck_Re, s=2, alpha=0.3, color='#FF5722')
    # Running mean (window 50)
    if len(abs_Ck_Re) > 50:
        sorted_idx = np.argsort(im_vals)
        im_sorted = im_vals[sorted_idx]
        ck_sorted = abs_Ck_Re[sorted_idx]
        window = 50
        running_mean = np.convolve(ck_sorted, np.ones(window)/window, mode='valid')
        im_mean = im_sorted[window//2:window//2+len(running_mean)]
        ax.plot(im_mean, running_mean, color='black', linewidth=2, label=f'running mean (w={window})')
        ax.legend(fontsize=10)
    ax.set_xlabel('Im(ρ_k)', fontsize=12)
    ax.set_ylabel('|C_k^Re|', fontsize=12)
    ax.set_title('Response envelope: decay, oscillation, or plateau?', fontsize=13)
    ax.grid(True, alpha=0.3)

    # (1,1) Anisotropy scatter
    ax = axes[1, 1]
    sc = ax.scatter(df_ok['Ck_Re'], df_ok['Ck_Im'],
                    c=df_ok['Im_rho_0'], cmap='viridis', s=5, alpha=0.5)
    ax.axhline(0, color='gray', linestyle='-', alpha=0.3)
    ax.axvline(0, color='gray', linestyle='-', alpha=0.3)
    ax.set_xlabel('C_k^Re', fontsize=12)
    ax.set_ylabel('C_k^Im', fontsize=12)
    ax.set_title('Anisotropy: Re vs Im response', fontsize=13)
    cbar = plt.colorbar(sc, ax=ax)
    cbar.set_label('Im(ρ_k)', fontsize=10)
    ax.grid(True, alpha=0.3)

    plt.suptitle(f'Phase 2: Bridge C Response Operator — {len(df_ok)} zeros\n'
                 f'ε = {eps:.0e}, D_logadd = {dla:.2e}', fontsize=15, y=1.02)
    plt.tight_layout()
    path = f'{outdir}/phase2_colab_overview.png'
    plt.savefig(path, dpi=150, bbox_inches='tight')
    plt.close()
    print(f"Saved: {path}")

    # --- Histogram of C_k^Re ---
    fig, axes = plt.subplots(1, 2, figsize=(14, 5))

    axes[0].hist(df_ok['Ck_Re'], bins=60, color='#FF5722', alpha=0.7, edgecolor='black')
    axes[0].axvline(0, color='blue', linestyle='--', alpha=0.5)
    axes[0].set_xlabel('C_k^Re', fontsize=12)
    axes[0].set_ylabel('count', fontsize=12)
    axes[0].set_title('Distribution of Re response', fontsize=13)

    axes[1].hist(df_ok['Ck_Im'], bins=60, color='#2196F3', alpha=0.7, edgecolor='black')
    axes[1].axvline(0, color='red', linestyle='--', alpha=0.5)
    axes[1].set_xlabel('C_k^Im', fontsize=12)
    axes[1].set_ylabel('count', fontsize=12)
    axes[1].set_title('Distribution of Im response', fontsize=13)

    plt.suptitle('Phase 2: Bridge C Response Distributions', fontsize=14)
    plt.tight_layout()
    path = f'{outdir}/phase2_colab_histograms.png'
    plt.savefig(path, dpi=150)
    plt.close()
    print(f"Saved: {path}")

    # --- Statistics ---
    print(f"\n{'='*60}")
    print(f"STATISTICS ({len(df_ok)} converged zeros)")
    print(f"{'='*60}")
    print(f"  C_k^Re:  mean={df_ok['Ck_Re'].mean():+.4f}, "
          f"std={df_ok['Ck_Re'].std():.4f}, "
          f"median={df_ok['Ck_Re'].median():+.4f}")
    print(f"  C_k^Im:  mean={df_ok['Ck_Im'].mean():+.4f}, "
          f"std={df_ok['Ck_Im'].std():.4f}, "
          f"median={df_ok['Ck_Im'].median():+.4f}")
    print(f"  |C_k^Re|: mean={np.abs(df_ok['Ck_Re']).mean():.4f}")
    print(f"  |C_k^Im|: mean={np.abs(df_ok['Ck_Im']).mean():.4f}")
    print(f"  Ratio |Re|/|Im| = {np.abs(df_ok['Ck_Re']).mean() / np.abs(df_ok['Ck_Im']).mean():.2f}")


def plot_stability(df_stab, outdir='/content'):
    eps_values = sorted(df_stab['epsilon'].unique())

    fig, axes = plt.subplots(1, 2, figsize=(14, 6))
    colors = plt.cm.viridis(np.linspace(0.2, 0.9, len(eps_values)))

    for eps_val, color in zip(eps_values, colors):
        sub = df_stab[df_stab['epsilon'] == eps_val].dropna()
        axes[0].scatter(sub['Im_rho_0'], sub['Ck_Re'], s=10, color=color,
                       alpha=0.6, label=f'ε={eps_val:.0e}')
        axes[1].scatter(sub['Im_rho_0'], sub['Ck_Im'], s=10, color=color,
                       alpha=0.6, label=f'ε={eps_val:.0e}')

    for ax, title in zip(axes, ['C_k^Re stability', 'C_k^Im stability']):
        ax.set_xlabel('Im(ρ_k)', fontsize=12)
        ax.set_title(title, fontsize=13)
        ax.legend(fontsize=9)
        ax.grid(True, alpha=0.3)

    plt.suptitle('Phase 2: C_k stability across ε (first 100 zeros)', fontsize=14)
    plt.tight_layout()
    path = f'{outdir}/phase2_colab_stability.png'
    plt.savefig(path, dpi=150)
    plt.close()
    print(f"Saved: {path}")

# ============================================================
# RUN
# ============================================================

if __name__ == '__main__':
    print("=" * 60)
    print("Phase 2 Colab: Bridge C Response Operator — Large Scale")
    print("=" * 60)

    # Check file exists
    if not os.path.exists(ZEROS_FILE):
        print(f"\n⚠️  {ZEROS_FILE} not found!")
        print("Upload zeros6.txt to /content/ first.")
        print("Falling back to built-in 25 zeros...")
        zeros_sampled = [
            14.134725142, 21.022039639, 25.010857580, 30.424876126,
            32.935061588, 37.586178159, 40.918719012, 43.327073281,
            48.005150881, 49.773832478, 52.970321478, 56.446247697,
            59.347044003, 60.831778525, 65.112544048, 67.079810529,
            69.546401711, 72.067157674, 75.704690699, 77.144840069,
            79.337375020, 82.910380854, 84.735492981, 87.425274613,
            88.809111208,
        ]
        all_zeros = zeros_sampled
    else:
        zeros_sampled, all_zeros = load_zeros(ZEROS_FILE, n_sample=N_SAMPLE)

    # Primary scan
    df_primary, dla = run_scan(zeros_sampled, eps_val=EPS_PRIMARY)

    outdir = '/content/drive/MyDrive'
    plot_all(df_primary, dla, EPS_PRIMARY, outdir=outdir)

    df_primary.to_csv(f'{outdir}/phase2_colab_primary_10.csv', index=False)
    print(f"Saved: {outdir}/phase2_colab_primary_10.csv")

    # Stability check (first 100)
    print("\n\nStability check...")
    df_stab = run_stability_check(zeros_sampled, eps_values=EPS_VALUES)
    plot_stability(df_stab, outdir=outdir)

    df_stab.to_csv(f'{outdir}/phase2_colab_stability_50.csv', index=False)
    print(f"Saved: {outdir}/phase2_colab_stability_50.csv")

    print("\n" + "=" * 60)
    print("DONE")
    print("=" * 60)
