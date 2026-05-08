import Mathlib
import GaussianWhoWhere.Infinite.LogDerivativeContinuityConcrete

/-!
# Log-derivative continuity from holomorphicity (Infinite L3)

Compresses the elementary continuity inputs of
`LogDerivativeContinuityConcrete` into a single global complex
differentiability hypothesis. The key analytic fact is

  `Differentiable ℂ Q  ⇒  Continuous (fun z => deriv Q z)`,

which we obtain from Mathlib's `DifferentiableOn.deriv` (the derivative
of a complex-differentiable function on an open set is itself
differentiable on that set) applied to the universal open set
`Set.univ`.

With this in hand, the sampled-input pipeline accepts a single
holomorphicity hypothesis instead of separate continuity hypotheses
on `Q` and `deriv Q`.
-/

noncomputable section

namespace GaussianWhoWhere

/-- A globally complex-differentiable function on `ℂ` has continuous
derivative. -/
theorem continuous_deriv_of_complex_differentiable
    {Q : ℂ → ℂ}
    (hQdiff : Differentiable ℂ Q) :
    Continuous (fun z : ℂ => deriv Q z) := by
  have hderivOn : DifferentiableOn ℂ (deriv Q) Set.univ :=
    hQdiff.differentiableOn.deriv isOpen_univ
  exact (differentiableOn_univ.mp hderivOn).continuous

/-- **Concrete witness for `LogDerivContinuousOnReal` from
holomorphicity.** Replaces the two elementary continuity hypotheses
of `LogDerivativeContinuityConcrete.lean` with the single hypothesis
`Differentiable ℂ Q`. -/
theorem logDerivContinuousOnReal_of_complex_differentiable
    {Q : ℂ → ℂ}
    (hQdiff : Differentiable ℂ Q)
    (hQnz : ∀ z : ℂ, Q z ≠ 0) :
    LogDerivContinuousOnReal Q :=
  logDerivContinuousOnReal_of_continuous_deriv
    (continuous_deriv_of_complex_differentiable hQdiff)
    hQdiff.continuous
    hQnz

/-- Sampled-input pipeline (dense-span form) consuming a single
holomorphicity hypothesis. -/
theorem complexLogDeriv_const_on_real_of_two_sampledWhoInputs_realShift_differentiable
    {DenseEnough : (ℕ → ℂ) → Prop}
    (hZD : ZeroDensityForcesZero DenseEnough)
    {Q : ℂ → ℂ}
    (hQ : FiniteExpType Q)
    (hQdiff : Differentiable ℂ Q)
    (hQnz : ∀ z : ℂ, Q z ≠ 0)
    (I : TwoSampledWhoInputs Q DenseEnough)
    {a b : ℝ}
    (ha : I.input₁.a = (a : ℂ))
    (hb : I.input₂.a = (b : ℂ))
    (hA : I.input₁.A ≠ 0) (hB : I.input₂.A ≠ 0)
    (hgen : TwoIncommensurablePeriodsGenerateDense a b) :
    ∀ x y : ℝ, complexLogDeriv Q (x : ℂ) = complexLogDeriv Q (y : ℂ) :=
  complexLogDeriv_const_on_real_of_two_sampledWhoInputs_realShift_continuousDeriv
    hZD hQ
    (continuous_deriv_of_complex_differentiable hQdiff)
    hQdiff.continuous
    hQnz I ha hb hA hB hgen

/-- Sampled-input pipeline for `TwoIncommensurableSampledWhoInputs`,
consuming a single holomorphicity hypothesis. -/
theorem complexLogDeriv_const_on_real_of_twoIncomm_sampled_differentiable
    {DenseEnough : (ℕ → ℂ) → Prop}
    (hZD : ZeroDensityForcesZero DenseEnough)
    {Q : ℂ → ℂ}
    (hQ : FiniteExpType Q)
    (hQdiff : Differentiable ℂ Q)
    (hQnz : ∀ z : ℂ, Q z ≠ 0)
    (I : TwoIncommensurableSampledWhoInputs Q DenseEnough)
    {a b : ℝ}
    (ha : I.inputs.input₁.a = (a : ℂ))
    (hb : I.inputs.input₂.a = (b : ℂ))
    (hA : I.inputs.input₁.A ≠ 0) (hB : I.inputs.input₂.A ≠ 0)
    (hgen : TwoIncommensurablePeriodsGenerateDense a b) :
    ∀ x y : ℝ, complexLogDeriv Q (x : ℂ) = complexLogDeriv Q (y : ℂ) :=
  complexLogDeriv_const_on_real_of_twoIncomm_sampled_continuousDeriv
    hZD hQ
    (continuous_deriv_of_complex_differentiable hQdiff)
    hQdiff.continuous
    hQnz I ha hb hA hB hgen

end GaussianWhoWhere
