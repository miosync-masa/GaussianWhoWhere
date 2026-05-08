import Mathlib
import GaussianWhoWhere.Infinite.LogDerivativeAlgebra

/-!
# Translation eigen → derivative eigen (Infinite L3, chain-rule step)

Internalizes the missing chain-rule step

  `RealTranslationEigen Q a A  ⇒  ∀ z, deriv Q (z + a) = A · deriv Q z`,

without any global differentiability hypothesis on `Q`. The proof
relies on Mathlib's

  `deriv_comp_add_const f a x : deriv (fun x => f (x + a)) x = deriv f (x + a)`,
  `deriv_const_mul_field u    : deriv (fun y => u * v y) x = u * deriv v x`,

both of which hold unconditionally for the *value* of `deriv` (with
differentiability concerns absorbed into Mathlib's
`differentiableAt`-aware `deriv` API).

With this step in hand, the explicit derivative-eigen hypotheses in
the `LogDerivativeAlgebra` constancy theorems become redundant; we
provide derivative-hypothesis-free variants and a small alias bridging
to Mathlib's `logDeriv`.
-/

noncomputable section

namespace GaussianWhoWhere

/-- **Chain-rule step.** A real translation eigen-relation on `Q`
propagates to its derivative. No differentiability hypothesis on `Q`
is needed: both Mathlib lemmas used below hold unconditionally on the
value of `deriv`. -/
theorem deriv_eigen_of_realTranslationEigen
    {Q : ℂ → ℂ} {a : ℝ} {A : ℂ}
    (heig : RealTranslationEigen Q a A) :
    ∀ z : ℂ, deriv Q (z + (a : ℂ)) = A * deriv Q z := by
  intro z
  -- The two functions z ↦ Q (z + a) and z ↦ A * Q z agree pointwise.
  have hfun : (fun w : ℂ => Q (w + (a : ℂ))) = fun w : ℂ => A * Q w := by
    funext w
    exact heig w
  -- Their derivatives at z therefore agree.
  have hderiv_eq :
      deriv (fun w : ℂ => Q (w + (a : ℂ))) z
        = deriv (fun w : ℂ => A * Q w) z := by
    rw [hfun]
  calc
    deriv Q (z + (a : ℂ))
        = deriv (fun w : ℂ => Q (w + (a : ℂ))) z :=
          (deriv_comp_add_const Q (a : ℂ) z).symm
    _ = deriv (fun w : ℂ => A * Q w) z := hderiv_eq
    _ = A * deriv Q z := deriv_const_mul_field A

/-- **Period of the candidate log-derivative from a real translation
eigen-relation alone.** No separate derivative-eigen hypothesis is
required; the chain-rule step is supplied by
`deriv_eigen_of_realTranslationEigen`. -/
theorem complexLogDeriv_period_of_realTranslationEigen
    {Q : ℂ → ℂ} {a : ℝ} {A : ℂ}
    (hQnz : ∀ z : ℂ, Q z ≠ 0)
    (hA : A ≠ 0)
    (heig : RealTranslationEigen Q a A) :
    LogDerivHasComplexRealPeriod Q (complexLogDeriv Q) a :=
  complexLogDeriv_period_of_deriv_eigen
    hQnz hA heig (deriv_eigen_of_realTranslationEigen heig)

/-- Interface form. -/
theorem complexLogDeriv_respects_realTranslationEigen
    {Q : ℂ → ℂ} {a : ℝ} {A : ℂ}
    (hQnz : ∀ z : ℂ, Q z ≠ 0)
    (hA : A ≠ 0) :
    LogDerivRespectsRealTranslationEigen Q (complexLogDeriv Q) a A := by
  intro heig
  exact complexLogDeriv_period_of_realTranslationEigen hQnz hA heig

/-- **Real-axis constancy from two value-level eigen-relations alone**
(dense-span form). The derivative-level eigen-relations are no longer
required as separate hypotheses. -/
theorem complexLogDeriv_const_on_real_of_two_realTranslationEigen_noDerivHyp_denseSpan
    {Q : ℂ → ℂ} {a b : ℝ} {A B : ℂ}
    (hcont : Continuous (RealRestrict (complexLogDeriv Q)))
    (hQnz : ∀ z : ℂ, Q z ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0)
    (heig_a : RealTranslationEigen Q a A)
    (heig_b : RealTranslationEigen Q b B)
    (hdense : Dense (IntegerPeriodSpan a b)) :
    ∀ x y : ℝ, complexLogDeriv Q (x : ℂ) = complexLogDeriv Q (y : ℂ) :=
  complexLogDeriv_const_on_real_of_two_realTranslationEigen_denseSpan
    hcont hQnz hA hB
    (deriv_eigen_of_realTranslationEigen heig_a)
    (deriv_eigen_of_realTranslationEigen heig_b)
    heig_a heig_b hdense

/-- Same conclusion consuming `TwoIncommensurablePeriodsGenerateDense`. -/
theorem complexLogDeriv_const_on_real_of_two_realTranslationEigen_noDerivHyp
    {Q : ℂ → ℂ} {a b : ℝ} {A B : ℂ}
    (hcont : Continuous (RealRestrict (complexLogDeriv Q)))
    (hQnz : ∀ z : ℂ, Q z ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0)
    (heig_a : RealTranslationEigen Q a A)
    (heig_b : RealTranslationEigen Q b B)
    (hgen : TwoIncommensurablePeriodsGenerateDense a b) :
    ∀ x y : ℝ, complexLogDeriv Q (x : ℂ) = complexLogDeriv Q (y : ℂ) :=
  complexLogDeriv_const_on_real_of_two_realTranslationEigen
    hcont hQnz hA hB
    (deriv_eigen_of_realTranslationEigen heig_a)
    (deriv_eigen_of_realTranslationEigen heig_b)
    heig_a heig_b hgen

/-- The project-local `complexLogDeriv` agrees pointwise with
Mathlib's `logDeriv`. -/
theorem complexLogDeriv_eq_logDeriv (Q : ℂ → ℂ) :
    complexLogDeriv Q = logDeriv Q := by
  funext z
  rw [logDeriv_apply]
  rfl

end GaussianWhoWhere
