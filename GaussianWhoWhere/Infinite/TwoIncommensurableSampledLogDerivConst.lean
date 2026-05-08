import GaussianWhoWhere.Infinite.SampledDefectToLogDerivConst

/-!
# Real-axis log-derivative constancy from `TwoIncommensurableSampledWhoInputs`
(Infinite L3)

Adds wrappers that consume `TwoIncommensurableSampledWhoInputs`
directly. These thread the existing
`SampledDefectToLogDerivConst` theorems through the bundle's
`.inputs` projection, so callers holding a packaged
incommensurable-sampled-who bundle can dispatch to log-derivative
constancy in one step.
-/

noncomputable section

namespace GaussianWhoWhere

/-- **Dense-span form** for `TwoIncommensurableSampledWhoInputs`. -/
theorem complexLogDeriv_const_on_real_of_twoIncommensurableSampledWhoInputs_realShift_denseSpan
    {DenseEnough : (ℕ → ℂ) → Prop}
    (hZD : ZeroDensityForcesZero DenseEnough)
    {Q : ℂ → ℂ}
    (hQ : FiniteExpType Q)
    (hLcont : LogDerivContinuousOnReal Q)
    (hQnz : ∀ z : ℂ, Q z ≠ 0)
    (I : TwoIncommensurableSampledWhoInputs Q DenseEnough)
    {a b : ℝ}
    (ha : I.inputs.input₁.a = (a : ℂ))
    (hb : I.inputs.input₂.a = (b : ℂ))
    (hA : I.inputs.input₁.A ≠ 0) (hB : I.inputs.input₂.A ≠ 0)
    (hdense : Dense (IntegerPeriodSpan a b)) :
    ∀ x y : ℝ, complexLogDeriv Q (x : ℂ) = complexLogDeriv Q (y : ℂ) :=
  complexLogDeriv_const_on_real_of_two_sampledWhoInputs_realShift_denseSpan
    hZD hQ hLcont hQnz I.inputs ha hb hA hB hdense

/-- Same conclusion consuming `TwoIncommensurablePeriodsGenerateDense`. -/
theorem complexLogDeriv_const_on_real_of_twoIncommensurableSampledWhoInputs_realShift
    {DenseEnough : (ℕ → ℂ) → Prop}
    (hZD : ZeroDensityForcesZero DenseEnough)
    {Q : ℂ → ℂ}
    (hQ : FiniteExpType Q)
    (hLcont : LogDerivContinuousOnReal Q)
    (hQnz : ∀ z : ℂ, Q z ≠ 0)
    (I : TwoIncommensurableSampledWhoInputs Q DenseEnough)
    {a b : ℝ}
    (ha : I.inputs.input₁.a = (a : ℂ))
    (hb : I.inputs.input₂.a = (b : ℂ))
    (hA : I.inputs.input₁.A ≠ 0) (hB : I.inputs.input₂.A ≠ 0)
    (hgen : TwoIncommensurablePeriodsGenerateDense a b) :
    ∀ x y : ℝ, complexLogDeriv Q (x : ℂ) = complexLogDeriv Q (y : ℂ) :=
  complexLogDeriv_const_on_real_of_two_sampledWhoInputs_realShift
    hZD hQ hLcont hQnz I.inputs ha hb hA hB hgen

end GaussianWhoWhere
