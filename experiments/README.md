# Bridge C Numerical Experiments

Numerical verification of the Bridge C Who-Where decomposition
and its connection to random matrix theory.

All experiments use the first 2,001,052 nontrivial zeros of the
Riemann zeta function (zeros6.txt from LMFDB).

## Requirements

- Python 3.10+
- `mpmath` (arbitrary precision arithmetic)
- `numpy`, `scipy`, `pandas`, `matplotlib`
- Google Colab with GPU is recommended for large runs (Phase 2)

## Zero data

Download `zeros6.txt` from [LMFDB](https://www.lmfdb.org/zeros/zeta/).
Not included in this repository due to size (~40 MB, 2,001,052 zeros).
Place in the working directory and update `ZEROS_FILE` in each script.

## Scripts and execution order

### 1. `phase2_bridge_c.py` — FE-breaking response operators

**What:** Perturbs ζ by breaking both multiplicativity and the functional
equation via Dirichlet coefficient modification. Tracks 100,000 zeros
and computes per-zero response operators C_k^Re, C_k^Im.

**Key result:** FE-broken perturbation releases both Re and Im
directions. |Re|/|Im| ≈ 1.08 at high heights.

**Runtime:** ~12 hours on Colab H100.

**Output:** `data/phase2_colab_primary_10.csv` (100K rows),
`data/phase2_colab_stability_10.csv`.

---

### 2. `phase1a_prime_v4.py` — FE-preserving response (Freezing Lemma)

**What:** Adds FE-preserving perturbation Ξ_ε(s) = Z(t) + ε·h(t) on
the critical line using the Hardy Z function. Since h(t) = h(t) is
real and Z(t) is real on the critical line, zeros move only in the
Im direction (δRe = 0 by the Freezing Lemma).

Computes C_k^Where = δt/ε ≈ −h(γ_k)/Z'(γ_k) for 10,000 zeros
across two h-functions (h=1, h=cos(t/T)) and two ε values (1e-5, 1e-6).

**Key results:**
- Perturbation theory verified: corr(predicted, measured) = 0.99999988
- Z'(γ_k) identified as Bridge C local stiffness
- Response values are Poisson-independent (autocorrelation ≈ 0)

**Runtime:** ~4 hours on Colab (4 conditions × 10K zeros).

**Output:** `data/phase1a_prime_v4.csv` (40K rows).

---

### 3. `phase2_vs_1a_comparison.py` — FE-preserved vs FE-broken

**What:** Compares the response distributions from Phase 2 (FE-broken)
and Phase 1a' (FE-preserved). Tests whether the Im-direction response
mechanism is the same with or without the functional equation.

**Requires:** `data/phase2_colab_primary_10.csv` and
`data/phase1a_prime_v4.csv`.

**Key results:**
- KS test confirms different distributions (p < 10^-67)
- FE preservation reduces variance and changes tail structure
- Both regimes show Poisson-like autocorrelation

**Runtime:** < 1 minute (reads precomputed CSVs).

**Config:** Set `PHASE2_RE_COL = 'Ck_Re'` and `PHASE2_IM_COL = 'Ck_Im'`
to override auto-detection of Phase 2 column names.

---

### 4. `bridge_c_rmt_stiffness.py` — GUE spacing vs Bridge C stiffness

**What:** Tests the stiffness-source hypothesis: does GUE level
repulsion control Bridge C local stiffness Z'(γ_k)?

Computes true adjacent spacings Δ_k from all 2M zeros, samples 2,000
zeros, computes Z'(γ_k), and correlates Δ_k with |Z'(γ_k)|.

**Key results:**
- Montgomery-Odlyzko confirmed: spacing ratio ⟨r⟩ = 0.607 ≈ GUE
- Δ_min vs |Z'|: Spearman r = +0.66, p = 10^-250
- Tail test: Mann-Whitney U = 0, softest zeros have universally
  smaller spacings than stiffest zeros
- Correlation stable across all height bins (r ≈ 0.67–0.75)

**Runtime:** ~15 minutes (Z' computation for 2K zeros).

---

### 5. `bridge_c_rmt_SI.py` — Supplementary analysis

**What:** Three additional verifications for the stiffness-source
hypothesis:

- **SI-1:** Geometric mean √(Δ_L·Δ_R) is a stronger predictor of
  |Z'| than Δ_min (r = 0.73 vs 0.66), consistent with Hadamard
  product structure.
- **SI-2:** Height-corrected regression. The spacing–stiffness
  correlation is robust within height bins (not a confound).
- **SI-3:** Softest zeros show left-right asymmetry: the next zero
  (right neighbor) tends to be closer (70% vs 30%), suggesting
  zero-pair structure.

**Runtime:** ~15 minutes.

**Output:** `data/bridge_c_rmt_SI_data.csv` (2K rows with Z' and
spacing data).

## Summary of confirmed results

| # | Result | Evidence |
|---|--------|----------|
| 1 | Freezing Lemma: δRe = 0 under FE-preserving perturbation | Theorem + 10K zeros, 8-digit agreement |
| 2 | Z'(γ_k) = Bridge C local stiffness | corr(pred, meas) = 0.99999988 |
| 3 | FE-preserved and FE-broken responses are distributionally distinct | KS p < 10^-67 |
| 4 | C_k^Where values are Poisson-independent | autocorrelation ≈ 0, all lags |
| 5 | GUE level repulsion controls Bridge C stiffness | Spearman r = 0.66, p = 10^-250 |
| 6 | √(Δ_L·Δ_R) is a stronger stiffness predictor than Δ_min | r = 0.73 vs 0.66 |
| 7 | Softest zeros show right-neighbor proximity (pair structure) | Wilcoxon p = 0.027 |

## Discarded hypothesis

| Hypothesis | Status | Reason |
|------------|--------|--------|
| β ladder (GOE for FE-preserved response) | Withdrawn | Predicted C_where is ε-independent; GOE-like spacing ratios in measured values were numerical artifacts |

The correct RMT connection is via the **stiffness-source hypothesis**:
GUE level repulsion controls the distribution of Z'(γ_k), not the
spacing-ratio universality class of the response values.
