import Mathlib
import GaussianWhoWhere.ConcretePolynomials
import GaussianWhoWhere.PolynomialRigidity

/-!
# Finite Hermite–Pochhammer uniqueness (Level 2)

The finite `P₄/P₈/P₁₂/P₁₆`-truncated who/where uniqueness theorem.
A multiplicative truncated deformation `Q4` collapses to `1`, hence
all coefficients vanish.

The argument has two pieces:

* `Q4Poly_eq_one_of_translation` lifts the rigidity theorem
  (`polynomial_translation_rigidity` from `PolynomialRigidity.lean`)
  to `Q4Poly`.
* `coeffs_zero_of_Q4Poly_eq_one` extracts `c₄ = c₈ = c₁₂ = c₁₆ = 0`
  by comparing `coeff` at degrees 8, 6, 4, 2.
-/

noncomputable section

namespace GaussianWhoWhere

open Polynomial

/-- Concrete finite Hermite–Pochhammer deformation truncated at `P₁₆`
(function-valued form). -/
def Q4 (c4 c8 c12 c16 : ℝ) (x : ℝ) : ℝ :=
  1 + c4 * P4 x + c8 * P8 x + c12 * P12 x + c16 * P16 x

/-- `Polynomial ℝ` form of `Q4`. -/
def Q4Poly (c4 c8 c12 c16 : ℝ) : Polynomial ℝ :=
  1 + C c4 * P4Poly + C c8 * P8Poly + C c12 * P12Poly + C c16 * P16Poly

@[simp] theorem eval_Q4Poly (c4 c8 c12 c16 : ℝ) (x : ℝ) :
    (Q4Poly c4 c8 c12 c16).eval x = Q4 c4 c8 c12 c16 x := by
  simp [Q4Poly, Q4]

/-- Translation rigidity for `Q4Poly`: a translation-multiplicative
deformation with value `1` at `0` and a nonzero translation step `a`
must be the constant polynomial `1`. -/
theorem Q4Poly_eq_one_of_translation
    (c4 c8 c12 c16 a : ℝ)
    (ha : a ≠ 0)
    (hQ0 : (Q4Poly c4 c8 c12 c16).eval 0 = 1)
    (htrans : ∀ x : ℝ,
      (Q4Poly c4 c8 c12 c16).eval (x + a)
        = (Q4Poly c4 c8 c12 c16).eval a
            * (Q4Poly c4 c8 c12 c16).eval x) :
    Q4Poly c4 c8 c12 c16 = 1 :=
  polynomial_translation_rigidity (Q4Poly c4 c8 c12 c16) a ha hQ0 htrans

/-- From `Q4Poly c4 c8 c12 c16 = 1` we extract that all coefficients
`c₄, c₈, c₁₂, c₁₆` vanish, by comparing coefficients at degrees
`8, 6, 4, 2`. -/
theorem coeffs_zero_of_Q4Poly_eq_one
    (c4 c8 c12 c16 : ℝ)
    (h : Q4Poly c4 c8 c12 c16 = 1) :
    c4 = 0 ∧ c8 = 0 ∧ c12 = 0 ∧ c16 = 0 := by
  -- Extract the degree-8 coefficient: only P16Poly contributes there,
  -- so coeff 8 = 65536 * c16 = 0, giving c16 = 0.
  have h8 : (Q4Poly c4 c8 c12 c16).coeff 8 = (1 : Polynomial ℝ).coeff 8 :=
    congrArg (fun p : Polynomial ℝ => p.coeff 8) h
  have hc16 : c16 = 0 := by
    simp [Q4Poly, P4Poly, P8Poly, P12Poly, P16Poly,
          coeff_add, coeff_sub, coeff_C_mul,
          coeff_X, coeff_X_pow, coeff_one] at h8
    linarith
  -- With c16 = 0, look at coeff 6: only P12Poly contributes the leading
  -- term, so 4096 * c12 = 0, giving c12 = 0.
  have h6 : (Q4Poly c4 c8 c12 c16).coeff 6 = (1 : Polynomial ℝ).coeff 6 :=
    congrArg (fun p : Polynomial ℝ => p.coeff 6) h
  have hc12 : c12 = 0 := by
    subst hc16
    simp [Q4Poly, P4Poly, P8Poly, P12Poly, P16Poly,
          coeff_add, coeff_sub, coeff_C_mul,
          coeff_X, coeff_X_pow, coeff_one] at h6
    linarith
  -- coeff 4: with c12 = c16 = 0, only P8Poly contributes leading 256 * c8.
  have h4 : (Q4Poly c4 c8 c12 c16).coeff 4 = (1 : Polynomial ℝ).coeff 4 :=
    congrArg (fun p : Polynomial ℝ => p.coeff 4) h
  have hc8 : c8 = 0 := by
    subst hc16; subst hc12
    simp [Q4Poly, P4Poly, P8Poly, P12Poly, P16Poly,
          coeff_add, coeff_sub, coeff_C_mul,
          coeff_X, coeff_X_pow, coeff_one] at h4
    linarith
  -- coeff 2: with c8 = c12 = c16 = 0, only P4Poly contributes 16 * c4.
  have h2 : (Q4Poly c4 c8 c12 c16).coeff 2 = (1 : Polynomial ℝ).coeff 2 :=
    congrArg (fun p : Polynomial ℝ => p.coeff 2) h
  have hc4 : c4 = 0 := by
    subst hc16; subst hc12; subst hc8
    simp [Q4Poly, P4Poly, P8Poly, P12Poly, P16Poly,
          coeff_add, coeff_sub, coeff_C_mul,
          coeff_X, coeff_X_pow, coeff_one] at h2
    linarith
  exact ⟨hc4, hc8, hc12, hc16⟩

/-- Finite `P₄/P₈/P₁₂/P₁₆` who/where uniqueness via translation rigidity.

Hypotheses are formulated at the polynomial level: a non-trivial
translation step `a ≠ 0` together with `Q4(0) = 1` and the translation
factorization at `a` implies all coefficients vanish. -/
theorem finite_concrete_uniqueness_P16_of_translation
    (c4 c8 c12 c16 a : ℝ)
    (ha : a ≠ 0)
    (hQ0 : (Q4Poly c4 c8 c12 c16).eval 0 = 1)
    (htrans : ∀ x : ℝ,
      (Q4Poly c4 c8 c12 c16).eval (x + a)
        = (Q4Poly c4 c8 c12 c16).eval a
            * (Q4Poly c4 c8 c12 c16).eval x) :
    c4 = 0 ∧ c8 = 0 ∧ c12 = 0 ∧ c16 = 0 :=
  coeffs_zero_of_Q4Poly_eq_one c4 c8 c12 c16
    (Q4Poly_eq_one_of_translation c4 c8 c12 c16 a ha hQ0 htrans)

/-- Finite `P₄/P₈/P₁₂/P₁₆` who/where uniqueness from full multiplicativity.

If the truncated deformation `Q4` is multiplicative under addition,
then all coefficients vanish. -/
theorem finite_concrete_uniqueness_P16
    (c4 c8 c12 c16 : ℝ)
    (hmul : ∀ x y : ℝ,
      Q4 c4 c8 c12 c16 (x + y)
        = Q4 c4 c8 c12 c16 x * Q4 c4 c8 c12 c16 y) :
    c4 = 0 ∧ c8 = 0 ∧ c12 = 0 ∧ c16 = 0 := by
  -- Step 1: Q4 0 = 1 from the multiplicativity hypothesis.
  -- Direct evaluation: Q4 c4 c8 c12 c16 0 = 1 + 0 + ... + 0 = 1
  -- because P4 0 = 12, P8 0 = 1680, etc. — but, more importantly,
  -- by definition `Q4 ... 0 = 1 + (linear combination of constants)`.
  -- We don't need to compute it: the rigidity route uses
  -- `htrans` derived from `hmul` with `y = 1`.
  -- However the constant term of Q4Poly at `eval 0` is not in general
  -- equal to 1 (it equals 1 + 12·c4 + 1680·c8 + 665280·c12 + 518918400·c16).
  -- Hence we cannot apply Q4Poly_eq_one_of_translation directly.
  -- Instead, take a different route via congrArg on the polynomial side.
  --
  -- Strategy: from hmul at (0, 0), deduce Q4 0 ∈ {0, 1}; combined with
  -- Q4Poly_eq_one_of_translation only when Q4 0 = 1.
  -- For the goal it suffices to show that Q4Poly = 1 directly.
  --
  -- Cleaner path: use Polynomial.funext on the multiplicativity at the
  -- polynomial level. But we are given `hmul` at values, not on polys.
  -- Instead use that for ANY a, htrans holds: take a = 1.
  have hQ0 : Q4 c4 c8 c12 c16 0 = 1 ∨ Q4 c4 c8 c12 c16 0 = 0 := by
    have hzz : Q4 c4 c8 c12 c16 0 = Q4 c4 c8 c12 c16 0 * Q4 c4 c8 c12 c16 0 := by
      have := hmul 0 0
      simpa using this
    -- Q4(0) * (Q4(0) - 1) = 0  ⇒  Q4(0) = 0 ∨ Q4(0) = 1
    have hfac : Q4 c4 c8 c12 c16 0 * (Q4 c4 c8 c12 c16 0 - 1) = 0 := by
      have := hzz
      ring_nf
      linarith
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inr h
    · exact Or.inl (by linarith)
  -- Either Q4(0) = 1 (rigidity case) or Q4(0) = 0 (forces all coeffs 0
  -- via direct argument). We handle both.
  rcases hQ0 with h0 | h0
  · -- Case Q4(0) = 1: apply rigidity with a = 1.
    have hQ0Poly : (Q4Poly c4 c8 c12 c16).eval 0 = 1 := by
      rw [eval_Q4Poly]; exact h0
    have htrans : ∀ x : ℝ,
        (Q4Poly c4 c8 c12 c16).eval (x + 1)
          = (Q4Poly c4 c8 c12 c16).eval 1
              * (Q4Poly c4 c8 c12 c16).eval x := by
      intro x
      simp only [eval_Q4Poly]
      have := hmul x 1
      linarith [mul_comm (Q4 c4 c8 c12 c16 x) (Q4 c4 c8 c12 c16 1)]
    exact finite_concrete_uniqueness_P16_of_translation
      c4 c8 c12 c16 1 one_ne_zero hQ0Poly htrans
  · -- Case Q4(0) = 0: then ∀ x, Q4 c4 c8 c12 c16 x = Q4 x * Q4 0 = 0,
    -- so Q4Poly evaluates to 0 everywhere, hence Q4Poly = 0; comparing
    -- coefficient 0 with `1 + 12·c4 + 1680·c8 + 665280·c12 + 518918400·c16`
    -- and degree-2 coefficients 16·c4 etc. we again get c4 = ⋯ = c16 = 0.
    -- Easier: ∀ x, Q4 x = 0, but then Q4 0 = 0 ≠ 1 — contradicts that
    -- Q4Poly = 0 has constant term 0 ≠ 1. We refute by direct calc.
    exfalso
    -- Q4 x = Q4 x * Q4 0 = Q4 x * 0 = 0
    have hzero : ∀ x : ℝ, Q4 c4 c8 c12 c16 x = 0 := by
      intro x
      have := hmul x 0
      rw [add_zero, h0, mul_zero] at this
      exact this
    -- But evaluating Q4 at any specific x gives a polynomial relation
    -- that combined with hzero yields a contradiction with the rest of
    -- the system. In particular hzero at x = 0 gives Q4 c4 c8 c12 c16 0 = 0,
    -- consistent with h0; the contradiction comes from `hmul 0 1`:
    -- Q4(1) = Q4(0) * Q4(1) = 0 * Q4(1) = 0, fine.
    -- We need a sharper argument. Use that `hzero` gives Q4Poly.eval x = 0 ∀x,
    -- hence Q4Poly = 0. But Q4Poly has natDegree ≤ 8 so that's fine; the
    -- argument is: the constant term of Q4Poly at coeff 0 is
    -- `1 + 12·c4 + 1680·c8 + 665280·c12 + 518918400·c16` — but with all
    -- c's free this is not obviously contradictory.
    -- Cleanest: derive Q4Poly = 0 from hzero, then compare coefficients
    -- (highest degree first) to get c16=c12=c8=c4=0; but then constant
    -- term becomes 1, contradicting Q4Poly = 0.
    have hQ4PolyZero : Q4Poly c4 c8 c12 c16 = 0 := by
      apply Polynomial.funext
      intro x
      simp only [eval_Q4Poly, Polynomial.eval_zero]
      exact hzero x
    -- From hQ4PolyZero, by a parallel coefficient argument we'd get
    -- c4 = c8 = c12 = c16 = 0 and the constant term reduces to 1, ≠ 0.
    -- Reuse coeffs_zero_of_Q4Poly_eq_one structure: degrees 8, 6, 4, 2
    -- still pin down c16, c12, c8, c4 because RHS is 0 instead of 1
    -- (coeff 8 of (0 : Polynomial ℝ) is also 0, same for degrees 6, 4, 2).
    have h8 : (Q4Poly c4 c8 c12 c16).coeff 8 = (0 : Polynomial ℝ).coeff 8 :=
      congrArg (fun p : Polynomial ℝ => p.coeff 8) hQ4PolyZero
    have hc16 : c16 = 0 := by
      simp [Q4Poly, P4Poly, P8Poly, P12Poly, P16Poly,
            coeff_add, coeff_sub, coeff_C_mul,
            coeff_X, coeff_X_pow, coeff_one] at h8
      linarith
    have h6 : (Q4Poly c4 c8 c12 c16).coeff 6 = (0 : Polynomial ℝ).coeff 6 :=
      congrArg (fun p : Polynomial ℝ => p.coeff 6) hQ4PolyZero
    have hc12 : c12 = 0 := by
      subst hc16
      simp [Q4Poly, P4Poly, P8Poly, P12Poly, P16Poly,
            coeff_add, coeff_sub, coeff_C_mul,
            coeff_X, coeff_X_pow, coeff_one] at h6
      linarith
    have h4 : (Q4Poly c4 c8 c12 c16).coeff 4 = (0 : Polynomial ℝ).coeff 4 :=
      congrArg (fun p : Polynomial ℝ => p.coeff 4) hQ4PolyZero
    have hc8 : c8 = 0 := by
      subst hc16; subst hc12
      simp [Q4Poly, P4Poly, P8Poly, P12Poly, P16Poly,
            coeff_add, coeff_sub, coeff_C_mul,
            coeff_X, coeff_X_pow, coeff_one] at h4
      linarith
    have h2 : (Q4Poly c4 c8 c12 c16).coeff 2 = (0 : Polynomial ℝ).coeff 2 :=
      congrArg (fun p : Polynomial ℝ => p.coeff 2) hQ4PolyZero
    have hc4 : c4 = 0 := by
      subst hc16; subst hc12; subst hc8
      simp [Q4Poly, P4Poly, P8Poly, P12Poly, P16Poly,
            coeff_add, coeff_sub, coeff_C_mul,
            coeff_X, coeff_X_pow, coeff_one] at h2
      linarith
    -- Now Q4Poly 0 0 0 0 = 1 (constant), but hQ4PolyZero says it's 0.
    subst hc16; subst hc12; subst hc8; subst hc4
    have hone : (1 : Polynomial ℝ) = 0 := by
      have hzero := hQ4PolyZero
      simp only [Q4Poly, P4Poly, P8Poly, P12Poly, P16Poly,
                 Polynomial.C_0, zero_mul, add_zero] at hzero
      exact hzero
    -- Compare constant coefficient: 1 ≠ 0 in ℝ.
    have hcoeff0 : (1 : Polynomial ℝ).coeff 0 = (0 : Polynomial ℝ).coeff 0 :=
      congrArg (fun p : Polynomial ℝ => p.coeff 0) hone
    simp at hcoeff0

end GaussianWhoWhere
