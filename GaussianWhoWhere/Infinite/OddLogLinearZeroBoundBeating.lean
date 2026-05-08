import Mathlib
import GaussianWhoWhere.Infinite.LogSampleZeroContradiction

/-!
# Odd-log specialization of the linear-beating sample (Infinite L3)

Specializes `LinearZeroBoundBeatingLogSample` to the concrete sample
sequence `oddLogComplexSample n = (Real.log (2n + 1) : ℂ)`.

The construction is:

* `sampleSet N := (Finset.range N).image oddLogSample`,
* `radius N := Real.log ((2N + 1 : ℕ) : ℝ)`.

The cardinality of `sampleSet N` is exactly `N` (the
`finite_many_odd_log_samples` lemma) and every element is bounded
above by the radius (`oddLogSample_le_of_index_lt`). The
nonzero-radius lower bound `0 ≤ oddLogSample n` for `n ≥ 0` together
with `2n + 1 ≥ 1` ensures the points lie in `[0, radius N]`.

The remaining `card_gt` field requires showing

  `∀ C ≥ 0, ∃ N : ℕ, C · log(2N + 1) + C < N`,

i.e. `log(2N+1) = o(N)`. This is internalized via Mathlib's
`Real.isLittleO_log_id_atTop`.
-/

noncomputable section

namespace GaussianWhoWhere

/-- **Asymptotic growth lemma.** Linear `N` eventually dominates
`C · log(2N + 1) + C`. The proof uses
`Real.isLittleO_log_id_atTop` to obtain a real-axis bound
`Real.log x ≤ ε · x` eventually as `x → ∞`, which transfers to the
`(2N + 1)`-form via `Tendsto.eventually`. -/
theorem eventually_linear_beats_log
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ N : ℕ, C * Real.log (((2 * N + 1 : ℕ) : ℝ)) + C < (N : ℝ) := by
  -- Pick ε = 1 / (4C + 4) > 0 (additive cushion lets us absorb C and 1).
  set ε : ℝ := 1 / (4 * C + 4) with hε_def
  have hε_pos : 0 < ε := by
    have : 0 < 4 * C + 4 := by linarith
    exact one_div_pos.mpr this
  -- Real.log =o[atTop] id ⇒ eventually ‖log x‖ ≤ ε · ‖id x‖.
  have hLittleO := Real.isLittleO_log_id_atTop.def hε_pos
  -- Transfer to atTop on ℕ via the embedding x ↦ ((2x + 1 : ℕ) : ℝ).
  have hcast_tendsto :
      Filter.Tendsto (fun N : ℕ => ((2 * N + 1 : ℕ) : ℝ))
        Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono ?_ tendsto_natCast_atTop_atTop
    intro N
    push_cast
    linarith
  have hev : ∀ᶠ N : ℕ in Filter.atTop,
      ‖Real.log (((2 * N + 1 : ℕ) : ℝ))‖
        ≤ ε * ‖((2 * N + 1 : ℕ) : ℝ)‖ :=
    hcast_tendsto.eventually hLittleO
  -- Strip absolute values: 2N+1 > 0 ⇒ ‖2N+1‖ = 2N+1, and we will work
  -- with the upper bound `log(2N+1) ≤ ε(2N+1)`.
  have hev' : ∀ᶠ N : ℕ in Filter.atTop,
      Real.log (((2 * N + 1 : ℕ) : ℝ))
        ≤ ε * ((2 * N + 1 : ℕ) : ℝ) := by
    filter_upwards [hev] with N hN
    have hpos : (0 : ℝ) < ((2 * N + 1 : ℕ) : ℝ) := by positivity
    have hlogpos_or : Real.log (((2 * N + 1 : ℕ) : ℝ))
        ≤ |Real.log (((2 * N + 1 : ℕ) : ℝ))| := le_abs_self _
    have habs_id : |((2 * N + 1 : ℕ) : ℝ)| = ((2 * N + 1 : ℕ) : ℝ) :=
      abs_of_pos hpos
    have hbound :
        |Real.log (((2 * N + 1 : ℕ) : ℝ))|
          ≤ ε * ((2 * N + 1 : ℕ) : ℝ) := by
      have hN' := hN
      simp only [Real.norm_eq_abs] at hN'
      rw [habs_id] at hN'
      exact hN'
    exact le_trans hlogpos_or hbound
  -- We also need N to be at least some explicit threshold to absorb
  -- the constant C and the +1 cushions.
  -- Choose N₀ via Filter.eventually_atTop on hev'.
  rcases Filter.eventually_atTop.mp hev' with ⟨N₀, hN₀⟩
  -- We are not done: we still need a *single concrete* N satisfying
  -- the stronger inequality `C * log(2N+1) + C < N`. Combine:
  --   log(2N+1) ≤ ε * (2N+1), so C * log(2N+1) ≤ C * ε * (2N+1).
  --   With ε = 1/(4C+4), C * ε * (2N+1) ≤ (2N+1)/4.
  -- We then need (2N+1)/4 + C < N, i.e. N > 2C + 1/2 + 1/2 (roughly).
  -- Pick N := max N₀ (4 * ⌈C⌉₊ + 4).
  set N : ℕ := max N₀ (4 * Nat.ceil C + 4) with hN_def
  have hN₀_le : N₀ ≤ N := le_max_left _ _
  have hN_lower : 4 * Nat.ceil C + 4 ≤ N := le_max_right _ _
  refine ⟨N, ?_⟩
  -- Apply hN₀ at N.
  have hlog_le : Real.log (((2 * N + 1 : ℕ) : ℝ))
      ≤ ε * ((2 * N + 1 : ℕ) : ℝ) := hN₀ N hN₀_le
  -- Multiply by C ≥ 0.
  have hC_log_le :
      C * Real.log (((2 * N + 1 : ℕ) : ℝ))
        ≤ C * (ε * ((2 * N + 1 : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left hlog_le hC
  -- Compute C * ε * (2N+1) ≤ (2N+1)/4 since C * ε ≤ 1/4.
  have hCε_le_quarter : C * ε ≤ 1 / 4 := by
    -- C * ε = C / (4C + 4) ≤ 1/4 since 4C ≤ 4C + 4.
    rw [hε_def]
    rw [show C * (1 / (4 * C + 4)) = C / (4 * C + 4) from by ring]
    have h4Cpos : (0 : ℝ) < 4 * C + 4 := by linarith
    rw [div_le_div_iff₀ h4Cpos (by norm_num : (0 : ℝ) < 4)]
    linarith
  have h2N1_nonneg : (0 : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) := by positivity
  have hCε_2N1 :
      C * (ε * ((2 * N + 1 : ℕ) : ℝ)) ≤ ((2 * N + 1 : ℕ) : ℝ) / 4 := by
    have := mul_le_mul_of_nonneg_right hCε_le_quarter h2N1_nonneg
    have hrw : C * (ε * ((2 * N + 1 : ℕ) : ℝ))
        = C * ε * ((2 * N + 1 : ℕ) : ℝ) := by ring
    rw [hrw]
    have hrw2 : (1 / 4 : ℝ) * ((2 * N + 1 : ℕ) : ℝ)
        = ((2 * N + 1 : ℕ) : ℝ) / 4 := by ring
    rw [← hrw2]
    exact this
  have hC_log_le' :
      C * Real.log (((2 * N + 1 : ℕ) : ℝ))
        ≤ ((2 * N + 1 : ℕ) : ℝ) / 4 :=
    le_trans hC_log_le hCε_2N1
  -- Final step: ((2N+1)/4) + C < N when N ≥ 4 * ⌈C⌉₊ + 4.
  -- (2N+1)/4 + C < N ⟺ 2N+1 + 4C < 4N ⟺ 4C + 1 < 2N
  -- ⟺ N > (4C + 1)/2 = 2C + 1/2. Since N ≥ 4⌈C⌉₊ + 4 ≥ 4C + 4 > 2C + 1/2.
  have hCeil : C ≤ (Nat.ceil C : ℝ) := Nat.le_ceil C
  have hN_real_ge : ((4 * Nat.ceil C + 4 : ℕ) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hN_lower
  have hN_ge_4C4 : (4 * C + 4 : ℝ) ≤ (N : ℝ) := by
    have hcast : ((4 * Nat.ceil C + 4 : ℕ) : ℝ)
        = 4 * (Nat.ceil C : ℝ) + 4 := by push_cast; ring
    rw [hcast] at hN_real_ge
    have : 4 * C + 4 ≤ 4 * (Nat.ceil C : ℝ) + 4 := by linarith
    linarith
  -- Combine: C * log + C ≤ (2N+1)/4 + C, want < N.
  have htarget : ((2 * N + 1 : ℕ) : ℝ) / 4 + C < (N : ℝ) := by
    have hcast : ((2 * N + 1 : ℕ) : ℝ) = 2 * (N : ℝ) + 1 := by
      push_cast; ring
    rw [hcast]
    linarith
  linarith

/-- **Concrete witness for `LinearZeroBoundBeatingLogSample` at the
odd-log sample sequence `oddLogComplexSample`.** -/
def oddLogLinearZeroBoundBeating :
    LinearZeroBoundBeatingLogSample oddLogComplexSample where
  sampleSet := fun N => (Finset.range N).image oddLogSample
  radius := fun N => Real.log (((2 * N + 1 : ℕ) : ℝ))
  radius_nonneg := by
    intro N
    have hge : (1 : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ 2 * N + 1 := by omega
      exact_mod_cast this
    exact Real.log_nonneg hge
  card_gt := by
    intro C hC
    rcases eventually_linear_beats_log C hC with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    rw [show ((Finset.range N).image oddLogSample).card = N from
        finite_many_odd_log_samples N]
    -- Goal: C * Real.log (((2 * N + 1 : ℕ) : ℝ)) + C < (N : ℝ).
    -- hN provides exactly this; just remove any cast residue.
    exact hN
  in_interval := by
    intro N x hx
    rcases Finset.mem_image.mp hx with ⟨n, hn, rfl⟩
    refine ⟨?_, ?_⟩
    · -- 0 ≤ oddLogSample n: log of a real ≥ 1.
      unfold oddLogSample
      have hge : (1 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
        have : (1 : ℕ) ≤ 2 * n + 1 := by omega
        exact_mod_cast this
      exact Real.log_nonneg hge
    · exact oddLogSample_le_of_index_lt (Finset.mem_range.mp hn)
  sampled := by
    intro N x hx
    rcases Finset.mem_image.mp hx with ⟨n, _, rfl⟩
    refine ⟨n, ?_⟩
    rfl

end GaussianWhoWhere
