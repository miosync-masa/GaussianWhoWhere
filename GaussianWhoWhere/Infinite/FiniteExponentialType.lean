import Mathlib

/-!
# Finite exponential type — closure properties (Infinite L3 base)

Mechanical, no-sorry foundation for the infinite Hermite–Pochhammer
extension. We define `FiniteExpType F`: the function `F : ℂ → ℂ` is
bounded by `C · exp(τ · ‖z‖)` for some nonnegative `C, τ`. Then we
prove the algebraic closure properties needed downstream:

* `finiteExpType_const`,
* `finiteExpType_translate`,
* `finiteExpType_const_mul`,
* `finiteExpType_add`,
* `finiteExpType_sub`.

These suffice to keep the residue function
`R_p(z) = Q(z + log p) − Q(log p) · Q(z)` inside the class once `Q`
is finite-exponential-type. No Jensen / zero-density / sample-density
content is touched here.
-/

noncomputable section

namespace GaussianWhoWhere

/-- A function `F : ℂ → ℂ` has **finite exponential type** if it is
bounded by `C · exp(τ · ‖z‖)` for some nonnegative constants
`C, τ : ℝ`. -/
def FiniteExpType (F : ℂ → ℂ) : Prop :=
  ∃ C τ : ℝ, 0 ≤ C ∧ 0 ≤ τ ∧
    ∀ z : ℂ, ‖F z‖ ≤ C * Real.exp (τ * ‖z‖)

theorem finiteExpType_const (c : ℂ) :
    FiniteExpType (fun _ : ℂ => c) := by
  refine ⟨‖c‖, 0, norm_nonneg c, le_refl 0, ?_⟩
  intro z
  -- ‖c‖ ≤ ‖c‖ * exp 0 = ‖c‖ * 1 = ‖c‖
  simp

theorem finiteExpType_translate {F : ℂ → ℂ}
    (hF : FiniteExpType F) (a : ℂ) :
    FiniteExpType (fun z => F (z + a)) := by
  obtain ⟨C, τ, hC, hτ, hbound⟩ := hF
  refine ⟨C * Real.exp (τ * ‖a‖), τ, ?_, hτ, ?_⟩
  · -- 0 ≤ C * exp (τ * ‖a‖)
    exact mul_nonneg hC (Real.exp_nonneg _)
  · intro z
    -- ‖F (z + a)‖ ≤ C * exp (τ * ‖z + a‖) ≤ C * exp (τ * (‖z‖ + ‖a‖))
    --             = (C * exp (τ * ‖a‖)) * exp (τ * ‖z‖)
    have hnorm : ‖z + a‖ ≤ ‖z‖ + ‖a‖ := norm_add_le z a
    have hexp_arg : τ * ‖z + a‖ ≤ τ * (‖z‖ + ‖a‖) :=
      mul_le_mul_of_nonneg_left hnorm hτ
    have hexp : Real.exp (τ * ‖z + a‖) ≤ Real.exp (τ * (‖z‖ + ‖a‖)) :=
      Real.exp_le_exp.mpr hexp_arg
    have hsplit : Real.exp (τ * (‖z‖ + ‖a‖))
        = Real.exp (τ * ‖z‖) * Real.exp (τ * ‖a‖) := by
      rw [show τ * (‖z‖ + ‖a‖) = τ * ‖z‖ + τ * ‖a‖ from by ring,
          Real.exp_add]
    -- Chain the bounds.
    calc ‖F (z + a)‖
        ≤ C * Real.exp (τ * ‖z + a‖) := hbound (z + a)
      _ ≤ C * Real.exp (τ * (‖z‖ + ‖a‖)) :=
            mul_le_mul_of_nonneg_left hexp hC
      _ = C * (Real.exp (τ * ‖z‖) * Real.exp (τ * ‖a‖)) := by rw [hsplit]
      _ = C * Real.exp (τ * ‖a‖) * Real.exp (τ * ‖z‖) := by ring

theorem finiteExpType_const_mul {F : ℂ → ℂ}
    (hF : FiniteExpType F) (c : ℂ) :
    FiniteExpType (fun z => c * F z) := by
  obtain ⟨C, τ, hC, hτ, hbound⟩ := hF
  refine ⟨‖c‖ * C, τ, mul_nonneg (norm_nonneg c) hC, hτ, ?_⟩
  intro z
  -- ‖c * F z‖ = ‖c‖ * ‖F z‖ ≤ ‖c‖ * (C * exp(τ‖z‖))
  --           = (‖c‖ * C) * exp(τ‖z‖)
  rw [norm_mul]
  calc ‖c‖ * ‖F z‖
      ≤ ‖c‖ * (C * Real.exp (τ * ‖z‖)) :=
        mul_le_mul_of_nonneg_left (hbound z) (norm_nonneg c)
    _ = ‖c‖ * C * Real.exp (τ * ‖z‖) := by ring

theorem finiteExpType_add {F G : ℂ → ℂ}
    (hF : FiniteExpType F) (hG : FiniteExpType G) :
    FiniteExpType (fun z => F z + G z) := by
  obtain ⟨C, τ, hC, hτ, hF_bound⟩ := hF
  obtain ⟨D, σ, hD, hσ, hG_bound⟩ := hG
  refine ⟨C + D, max τ σ, add_nonneg hC hD, le_max_of_le_left hτ, ?_⟩
  intro z
  set μ : ℝ := max τ σ
  have hμτ : τ ≤ μ := le_max_left τ σ
  have hμσ : σ ≤ μ := le_max_right τ σ
  have hzn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  -- Bound F z and G z each by their exp(μ · ‖z‖) version.
  have hF_le : ‖F z‖ ≤ C * Real.exp (μ * ‖z‖) := by
    calc ‖F z‖
        ≤ C * Real.exp (τ * ‖z‖) := hF_bound z
      _ ≤ C * Real.exp (μ * ‖z‖) :=
            mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hμτ hzn)) hC
  have hG_le : ‖G z‖ ≤ D * Real.exp (μ * ‖z‖) := by
    calc ‖G z‖
        ≤ D * Real.exp (σ * ‖z‖) := hG_bound z
      _ ≤ D * Real.exp (μ * ‖z‖) :=
            mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hμσ hzn)) hD
  -- ‖F z + G z‖ ≤ ‖F z‖ + ‖G z‖ ≤ (C + D) * exp(μ‖z‖)
  calc ‖F z + G z‖
      ≤ ‖F z‖ + ‖G z‖ := norm_add_le _ _
    _ ≤ C * Real.exp (μ * ‖z‖) + D * Real.exp (μ * ‖z‖) :=
          add_le_add hF_le hG_le
    _ = (C + D) * Real.exp (μ * ‖z‖) := by ring

theorem finiteExpType_sub {F G : ℂ → ℂ}
    (hF : FiniteExpType F) (hG : FiniteExpType G) :
    FiniteExpType (fun z => F z - G z) := by
  -- F - G = F + (-1) * G; reduce via add + const_mul.
  have hG' : FiniteExpType (fun z => (-1 : ℂ) * G z) :=
    finiteExpType_const_mul hG (-1)
  have hadd : FiniteExpType (fun z => F z + (-1 : ℂ) * G z) :=
    finiteExpType_add hF hG'
  -- The function `fun z => F z - G z` equals `fun z => F z + (-1) * G z`.
  have heq : (fun z => F z - G z) = fun z => F z + (-1 : ℂ) * G z := by
    funext z
    ring
  rw [heq]
  exact hadd

end GaussianWhoWhere
