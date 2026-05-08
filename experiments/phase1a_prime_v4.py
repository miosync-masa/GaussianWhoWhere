#!/usr/bin/env python3
#Phase 1a' v4: Hardy Z + Bridge C Stiffness Analysis

import mpmath as mp
import numpy as np
import matplotlib.pyplot as plt
import pandas as pd
from scipy import stats
import time
import os

mp.mp.dps = 30

# ============================================================
# Config
# ============================================================

ZEROS_FILE = '/content/zeros6.txt'
N_SAMPLE = 10000
SEED = 42
EPS_VALUES = [1e-6, 1e-5]
MAX_LOCAL_SHIFT = mp.mpf("1e-3")

# ============================================================
# Load zeros (with spacing computation)
# ============================================================

def load_zeros(path, n_sample=N_SAMPLE, seed=SEED):
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
    print(f"  Total: {len(zeros)}")
    zeros = sorted(zeros)

    rng = np.random.RandomState(seed)
    if len(zeros) > n_sample:
        indices = sorted(rng.choice(len(zeros), n_sample, replace=False))
        sampled = [zeros[i] for i in indices]
    else:
        sampled = zeros

    # Compute spacings for sampled zeros
    # Note: these are spacings between SAMPLED zeros, not consecutive
    # For true spacing, we'd need all zeros. But this gives local density.
    spacings = np.diff(sampled)

    print(f"  Sampled: {len(sampled)}, Range: [{sampled[0]:.2f}, {sampled[-1]:.2f}]")
    print(f"  Median inter-sample spacing: {np.median(spacings):.2f}")
    return sampled, spacings

# ============================================================
# Hardy Z function
# ============================================================

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

# ============================================================
# h functions
# ============================================================

def make_h_functions(zeros_sampled):
    T = mp.mpf(max(abs(t) for t in zeros_sampled))
    return {
        "h=1": lambda t: mp.mpf(1),
        "h=cos(t/T)": lambda t, T=T: mp.cos(mp.mpf(t) / T),
    }

# ============================================================
# Predicted displacement
# ============================================================

def predicted_delta_t(h_func, eps, t0):
    t0 = mp.mpf(t0)
    eps = mp.mpf(eps)
    zp = hardy_Z_prime(t0)
    h0 = h_func(t0)
    if zp == 0:
        return mp.nan, zp, h0
    dt = -eps * h0 / zp
    return dt, zp, h0

# ============================================================
# 1D zero tracking
# ============================================================

def track_zero_line(h_func, eps, t0):
    t0_mp = mp.mpf(t0)
    eps_mp = mp.mpf(eps)

    dt_pred, zp, h0 = predicted_delta_t(h_func, eps_mp, t0_mp)

    if not mp.isfinite(dt_pred):
        return {"ok": False, "status": "bad_prediction",
                "t": np.nan, "delta_pred": np.nan,
                "Z_prime": float(zp) if mp.isfinite(zp) else np.nan,
                "h0": float(h0) if mp.isfinite(h0) else np.nan,
                "residual_abs": np.nan}

    if abs(dt_pred) > MAX_LOCAL_SHIFT:
        return {"ok": False, "status": "nonlocal",
                "t": np.nan, "delta_pred": float(dt_pred),
                "Z_prime": float(zp), "h0": float(h0),
                "residual_abs": np.nan}

    t_guess = t0_mp + dt_pred

    def f(t):
        return hardy_Z(t) + eps_mp * h_func(t)

    try:
        step = max(abs(dt_pred) * mp.mpf("0.1"), mp.mpf("1e-10"))
        t_root = mp.findroot(f, (t_guess - step, t_guess + step),
                             tol=mp.mpf("1e-25"), maxsteps=50)
        residual = f(t_root)
        return {"ok": True, "status": "ok",
                "t": float(t_root), "delta_pred": float(dt_pred),
                "Z_prime": float(zp), "h0": float(h0),
                "residual_abs": float(abs(residual))}
    except:
        return {"ok": False, "status": "findroot_failed",
                "t": np.nan, "delta_pred": float(dt_pred),
                "Z_prime": float(zp), "h0": float(h0),
                "residual_abs": np.nan}

# ============================================================
# Main scan with extended columns
# ============================================================

def run_scan(zeros_sampled, spacings, h_name, h_func, eps):
    print(f"\n{'='*60}")
    print(f"h = {h_name}, ε = {eps:.0e}")
    print(f"{'='*60}")

    records = []
    t_start = time.time()
    n_ok = n_nonlocal = n_failed = 0

    for i, t0 in enumerate(zeros_sampled):
        result = track_zero_line(h_func, eps, t0)

        if result["ok"]:
            n_ok += 1
            delta_Im = result["t"] - t0
            dt_pred = result["delta_pred"]
            err = abs(delta_Im - dt_pred)
        else:
            delta_Im = np.nan
            dt_pred = result["delta_pred"] if isinstance(result["delta_pred"], float) else np.nan
            err = np.nan
            if result["status"] == "nonlocal":
                n_nonlocal += 1
            else:
                n_failed += 1

        # Z' and stiffness
        zp = result["Z_prime"]
        inv_abs_zp = 1.0 / abs(zp) if (not np.isnan(zp) and abs(zp) > 0) else np.nan

        # C_where
        c_where = delta_Im / eps if (result["ok"] and eps > 0) else np.nan
        c_where_pred = -result["h0"] / zp if (not np.isnan(zp) and abs(zp) > 0
                                               and not np.isnan(result["h0"])) else np.nan

        # Spacing
        spacing_prev = spacings[i-1] if i > 0 and i-1 < len(spacings) else np.nan
        spacing_next = spacings[i] if i < len(spacings) else np.nan
        local_spacing = min(s for s in [spacing_prev, spacing_next]
                           if not np.isnan(s)) if not (
                           np.isnan(spacing_prev) and np.isnan(spacing_next)) else np.nan

        records.append({
            "h_type": h_name, "epsilon": eps, "k": i+1,
            "gamma_0": t0, "status": result["status"],
            "delta_Im": delta_Im, "delta_pred_Im": dt_pred,
            "delta_Im_error": err,
            "Z_prime": zp,
            "inv_abs_Z_prime": inv_abs_zp,
            "h0": result["h0"],
            "C_where": c_where,
            "C_where_pred": c_where_pred,
            "spacing_prev": spacing_prev,
            "spacing_next": spacing_next,
            "local_spacing": local_spacing,
            "residual_abs": result["residual_abs"],
        })

        if (i+1) % 200 == 0:
            elapsed = time.time() - t_start
            rate = (i+1) / elapsed
            remaining = (len(zeros_sampled) - i - 1) / rate
            print(f"  [{i+1}/{len(zeros_sampled)}] "
                  f"{elapsed:.0f}s, ~{remaining:.0f}s left, "
                  f"{n_ok} ok, {n_nonlocal} nl, {n_failed} fail")

    elapsed = time.time() - t_start
    df = pd.DataFrame(records)
    df_ok = df[df['status'] == 'ok']

    print(f"\nDone in {elapsed:.1f}s")
    print(f"  OK={n_ok}, Nonlocal={n_nonlocal}, Failed={n_failed}")

    if len(df_ok) > 0:
        corr = np.corrcoef(df_ok['delta_pred_Im'], df_ok['delta_Im'])[0,1]
        med_err = np.nanmedian(df_ok['delta_Im_error'])
        med_shift = np.nanmedian(np.abs(df_ok['delta_Im']))
        print(f"  corr(pred, meas) = {corr:.8f}")
        print(f"  median relative error = {med_err/(med_shift+1e-50):.4e}")
        if corr > 0.999:
            print(f"  *** PERTURBATION THEORY VERIFIED ✓ ***")

    return df

# ============================================================
# Bridge C Stiffness Analysis
# ============================================================

def analyze_stiffness(df_all, outdir):
    df_ok = df_all[df_all['status'] == 'ok'].copy()
    if len(df_ok) == 0:
        print("No OK data!")
        return

    # Use first H, first eps for stiffness analysis
    h0 = df_ok['h_type'].unique()[0]
    e0 = df_ok['epsilon'].unique()[0]
    sub = df_ok[(df_ok['h_type'] == h0) & (df_ok['epsilon'] == e0)].copy()

    print(f"\n{'='*60}")
    print(f"BRIDGE C STIFFNESS ANALYSIS (N={len(sub)})")
    print(f"{'='*60}")

    fig, axes = plt.subplots(2, 3, figsize=(18, 12))

    # (0,0) |Z'(γ)| vs γ
    ax = axes[0, 0]
    ax.scatter(sub['gamma_0'], np.abs(sub['Z_prime']), s=3, alpha=0.3, color='#2196F3')
    ax.set_xlabel('γ', fontsize=11)
    ax.set_ylabel("|Z'(γ)|", fontsize=11)
    ax.set_title("Bridge C stiffness vs zero height", fontsize=12)
    ax.set_yscale('log')
    ax.grid(True, which='both', alpha=0.3)

    # (0,1) 1/|Z'(γ)| distribution (heavy tail source?)
    ax = axes[0, 1]
    inv_zp = sub['inv_abs_Z_prime'].dropna()
    ax.hist(np.log10(inv_zp[inv_zp > 0]), bins=50, color='#FF5722',
            alpha=0.7, edgecolor='black')
    ax.set_xlabel("log₁₀(1/|Z'(γ)|)", fontsize=11)
    ax.set_ylabel('count', fontsize=11)
    ax.set_title("Inverse stiffness distribution\n(right tail = weak stiffness = large response)",
                 fontsize=11)
    ax.grid(True, alpha=0.3)

    # (0,2) |Z'(γ)| vs local spacing
    ax = axes[0, 2]
    sp = sub['local_spacing'].dropna()
    zp_sp = np.abs(sub.loc[sp.index, 'Z_prime'])
    ax.scatter(sp, zp_sp, s=3, alpha=0.3, color='#4CAF50')
    ax.set_xlabel('local spacing', fontsize=11)
    ax.set_ylabel("|Z'(γ)|", fontsize=11)
    ax.set_title("|Z'| vs spacing\n(RMT repulsion → stiffness?)", fontsize=12)
    ax.set_yscale('log')
    ax.grid(True, which='both', alpha=0.3)
    if len(sp) > 10:
        r_sp, p_sp = stats.pearsonr(sp, zp_sp)
        ax.set_title(f"|Z'| vs spacing (r={r_sp:.3f}, p={p_sp:.2e})", fontsize=11)

    # (1,0) C_where adjacent correlation
    ax = axes[1, 0]
    cw = sub['C_where'].dropna().values
    if len(cw) > 10:
        ax.scatter(cw[:-1], cw[1:], s=3, alpha=0.3, color='#9C27B0')
        r_adj, p_adj = stats.pearsonr(cw[:-1], cw[1:])
        ax.set_title(f"C_where adjacent: r={r_adj:.4f} (p={p_adj:.2e})", fontsize=11)
    ax.set_xlabel('C_k^Where', fontsize=11)
    ax.set_ylabel('C_{k+1}^Where', fontsize=11)
    ax.axhline(0, color='gray', alpha=0.3)
    ax.axvline(0, color='gray', alpha=0.3)
    ax.grid(True, alpha=0.3)

    # (1,1) C_where distribution
    ax = axes[1, 1]
    if len(cw) > 0:
        ax.hist(cw, bins=50, color='#9C27B0', alpha=0.7, edgecolor='black', density=True)
        ax.set_xlabel('C_k^Where', fontsize=11)
        ax.set_ylabel('density', fontsize=11)
        ax.set_title(f'C_where distribution (skew={stats.skew(cw):.2f}, '
                    f'kurt={stats.kurtosis(cw):.2f})', fontsize=11)
    ax.grid(True, alpha=0.3)

    # (1,2) δIm predicted vs measured (confirmation)
    ax = axes[1, 2]
    ax.scatter(sub['delta_pred_Im'], sub['delta_Im'], s=3, alpha=0.3, color='#4CAF50')
    lim = max(abs(sub['delta_pred_Im']).max(), abs(sub['delta_Im']).max()) * 1.1
    if lim > 0:
        ax.plot([-lim, lim], [-lim, lim], 'r--', lw=2, label='perfect prediction')
    corr = np.corrcoef(sub['delta_pred_Im'], sub['delta_Im'])[0, 1]
    ax.set_title(f'Perturbation theory: r={corr:.6f}', fontsize=11)
    ax.set_xlabel('δt predicted', fontsize=11)
    ax.set_ylabel('δt measured', fontsize=11)
    ax.legend(fontsize=9)
    ax.grid(True, alpha=0.3)

    plt.suptitle(f"Phase 1a\' v4: Bridge C Stiffness Analysis\n"
                 f"{h0}, ε={e0:.0e}, N={len(sub)}", fontsize=14, y=1.02)
    plt.tight_layout()
    path = f'{outdir}/phase1a_prime_v4_stiffness.png'
    plt.savefig(path, dpi=150, bbox_inches='tight')
    plt.close()
    print(f"Saved: {path}")

    # Print statistics
    print(f"\n  |Z'(γ)| statistics:")
    print(f"    mean = {np.mean(np.abs(sub['Z_prime'])):.4e}")
    print(f"    median = {np.median(np.abs(sub['Z_prime'])):.4e}")
    print(f"    std = {np.std(np.abs(sub['Z_prime'])):.4e}")

    print(f"\n  1/|Z'(γ)| (inverse stiffness):")
    print(f"    mean = {np.mean(inv_zp):.4e}")
    print(f"    median = {np.median(inv_zp):.4e}")
    print(f"    skew = {stats.skew(inv_zp):.4f}")
    print(f"    kurt = {stats.kurtosis(inv_zp):.4f}")

    if len(cw) > 10:
        r_adj, p_adj = stats.pearsonr(cw[:-1], cw[1:])
        print(f"\n  C_where adjacent correlation: r={r_adj:.4f} (p={p_adj:.2e})")
        print(f"  C_where skew = {stats.skew(cw):.4f}")
        print(f"  C_where kurt = {stats.kurtosis(cw):.4f}")

    if len(sp) > 10 and len(zp_sp) > 10:
        r_sp, p_sp = stats.pearsonr(sp, zp_sp)
        print(f"\n  |Z'| vs spacing correlation: r={r_sp:.4f} (p={p_sp:.2e})")

# ============================================================
# Standard plots
# ============================================================

def plot_results(df_all, outdir):
    df_ok = df_all[df_all['status'] == 'ok'].copy()
    if len(df_ok) == 0:
        return

    h_types = df_ok['h_type'].unique()
    eps_values = sorted(df_ok['epsilon'].unique())

    # Summary table
    print(f"\n{'='*60}")
    print("FINAL SUMMARY")
    print(f"{'='*60}")
    for h_name in h_types:
        for eps in eps_values:
            sub = df_ok[(df_ok['h_type'] == h_name) & (df_ok['epsilon'] == eps)]
            sub_all = df_all[(df_all['h_type'] == h_name) & (df_all['epsilon'] == eps)]
            if len(sub) > 0:
                corr = np.corrcoef(sub['delta_pred_Im'], sub['delta_Im'])[0,1]
                med_err = np.nanmedian(sub['delta_Im_error'])
                med_shift = np.nanmedian(np.abs(sub['delta_Im']))
                n_nl = (sub_all['status'] == 'nonlocal').sum()
                print(f"\n  {h_name}, ε={eps:.0e}:")
                print(f"    OK={len(sub)}, Nonlocal={n_nl}")
                print(f"    corr(pred, meas) = {corr:.8f}")
                print(f"    median relative error = {med_err/(med_shift+1e-50):.4e}")

# ============================================================
# RUN
# ============================================================

if __name__ == '__main__':
    print("=" * 60)
    print("Phase 1a' v4: Hardy Z + Bridge C Stiffness")
    print("=" * 60)

    if not os.path.exists(ZEROS_FILE):
        print(f"⚠️ {ZEROS_FILE} not found!")
        exit(1)

    zeros_sampled, spacings = load_zeros(ZEROS_FILE, n_sample=N_SAMPLE)
    H_FUNCTIONS = make_h_functions(zeros_sampled)

    outdir = '/content/drive/MyDrive'
    if not os.path.exists(outdir):
        outdir = '/content'

    all_dfs = []
    for h_name, h_func in H_FUNCTIONS.items():
        for eps in EPS_VALUES:
            df = run_scan(zeros_sampled, spacings, h_name, h_func, eps)
            all_dfs.append(df)

    df_all = pd.concat(all_dfs, ignore_index=True)

    # Standard results
    plot_results(df_all, outdir)

    # Bridge C stiffness analysis
    analyze_stiffness(df_all, outdir)

    # Save
    csv_path = f'{outdir}/phase1a_prime_v4.csv'
    df_all.to_csv(csv_path, index=False)
    print(f"\nSaved: {csv_path}")
