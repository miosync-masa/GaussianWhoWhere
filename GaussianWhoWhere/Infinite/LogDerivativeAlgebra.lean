import Mathlib
import GaussianWhoWhere.Infinite.TranslationEigenLogDerivInterface

/-!
# Log-derivative algebraic cancellation (Infinite L3)

We define the candidate log-derivative

  `complexLogDeriv Q z := deriv Q z / Q z`

and prove the algebraic step:

> If `Q(z + a) = A · Q(z)` and `deriv Q (z + a) = A · deriv Q (z)` for
> all `z`, with `Q` nonvanishing and `A ≠ 0`, then
> `complexLogDeriv Q (z + a) = complexLogDeriv Q z`.

The chain-rule / derivative-eigen step itself
(`heig ⇒ ∀ z, deriv Q (z + a) = A · deriv Q z`) is **not** undertaken
here; this file only does the algebraic cancellation that *follows*
once the derivative eigen-relation is supplied.
-/

noncomputable section

namespace GaussianWhoWhere

/-- The candidate complex log-derivative `Q'/Q`. -/
def complexLogDeriv (Q : ℂ → ℂ) : ℂ → ℂ :=
  fun z => deriv Q z / Q z

/-- **Algebraic period.** Once both the value-level and the
derivative-level eigen-relations have been supplied (and `Q` is
nonvanishing with `A ≠ 0`), the candidate log-derivative inherits a
complex-level real period. -/
theorem complexLogDeriv_period_of_deriv_eigen
    {Q : ℂ → ℂ} {a : ℝ} {A : ℂ}
    (hQnz : ∀ z : ℂ, Q z ≠ 0)
    (hA : A ≠ 0)
    (heig : RealTranslationEigen Q a A)
    (hderiv_eig : ∀ z : ℂ, deriv Q (z + (a : ℂ)) = A * deriv Q z) :
    LogDerivHasComplexRealPeriod Q (complexLogDeriv Q) a := by
  intro z
  unfold complexLogDeriv
  rw [hderiv_eig z, heig z]
  field_simp [hA, hQnz z]

/-- Interface form of the algebraic-period result. -/
theorem complexLogDeriv_respects_realTranslationEigen_of_deriv_eigen
    {Q : ℂ → ℂ} {a : ℝ} {A : ℂ}
    (hQnz : ∀ z : ℂ, Q z ≠ 0)
    (hA : A ≠ 0)
    (hderiv_eig : ∀ z : ℂ, deriv Q (z + (a : ℂ)) = A * deriv Q z) :
    LogDerivRespectsRealTranslationEigen Q (complexLogDeriv Q) a A := by
  intro heig
  exact complexLogDeriv_period_of_deriv_eigen hQnz hA heig hderiv_eig

/-- **Real-axis constancy of `complexLogDeriv Q`, dense-span form.**
Two value-level eigen-relations together with their derivative-level
counterparts (and continuity of the real restriction, nonvanishing of
`Q`, nonzero eigenvalues, dense integer span of the shifts) force
`complexLogDeriv Q` to take a single value on the real axis. -/
theorem complexLogDeriv_const_on_real_of_two_realTranslationEigen_denseSpan
    {Q : ℂ → ℂ} {a b : ℝ} {A B : ℂ}
    (hcont : Continuous (RealRestrict (complexLogDeriv Q)))
    (hQnz : ∀ z : ℂ, Q z ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0)
    (hderiv_a : ∀ z : ℂ, deriv Q (z + (a : ℂ)) = A * deriv Q z)
    (hderiv_b : ∀ z : ℂ, deriv Q (z + (b : ℂ)) = B * deriv Q z)
    (heig_a : RealTranslationEigen Q a A)
    (heig_b : RealTranslationEigen Q b B)
    (hdense : Dense (IntegerPeriodSpan a b)) :
    ∀ x y : ℝ, complexLogDeriv Q (x : ℂ) = complexLogDeriv Q (y : ℂ) :=
  logDeriv_const_on_real_of_two_realTranslationEigen_denseSpan
    hcont
    (complexLogDeriv_respects_realTranslationEigen_of_deriv_eigen hQnz hA hderiv_a)
    (complexLogDeriv_respects_realTranslationEigen_of_deriv_eigen hQnz hB hderiv_b)
    heig_a heig_b hdense

/-- **Real-axis constancy of `complexLogDeriv Q`, arithmetic-density
form.** Variant consuming `TwoIncommensurablePeriodsGenerateDense`. -/
theorem complexLogDeriv_const_on_real_of_two_realTranslationEigen
    {Q : ℂ → ℂ} {a b : ℝ} {A B : ℂ}
    (hcont : Continuous (RealRestrict (complexLogDeriv Q)))
    (hQnz : ∀ z : ℂ, Q z ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0)
    (hderiv_a : ∀ z : ℂ, deriv Q (z + (a : ℂ)) = A * deriv Q z)
    (hderiv_b : ∀ z : ℂ, deriv Q (z + (b : ℂ)) = B * deriv Q z)
    (heig_a : RealTranslationEigen Q a A)
    (heig_b : RealTranslationEigen Q b B)
    (hgen : TwoIncommensurablePeriodsGenerateDense a b) :
    ∀ x y : ℝ, complexLogDeriv Q (x : ℂ) = complexLogDeriv Q (y : ℂ) :=
  logDeriv_const_on_real_of_two_realTranslationEigen
    hcont
    (complexLogDeriv_respects_realTranslationEigen_of_deriv_eigen hQnz hA hderiv_a)
    (complexLogDeriv_respects_realTranslationEigen_of_deriv_eigen hQnz hB hderiv_b)
    heig_a heig_b hgen

end GaussianWhoWhere
