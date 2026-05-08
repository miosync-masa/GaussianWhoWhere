import GaussianWhoWhere.Infinite.KroneckerDensity
import GaussianWhoWhere.Infinite.GlobalLogDerivConstToExpInterface

/-!
# Kronecker pipeline (Infinite L3)

Replaces the density predicate `TwoIncommensurablePeriodsGenerateDense
a b` in the final C3 pipeline by the concrete hypothesis
`Irrational (a / b)`, by routing through
`twoIncommensurablePeriodsGenerateDense_of_irrational_div`.

This eliminates one of the previous five named analytic interfaces:
the Kronecker density predicate is now derivable from an
irrationality input on the shift ratio.
-/

noncomputable section

namespace GaussianWhoWhere

/-- **Sampled-input pipeline → exponential survivor, with irrational
ratio.** Same conclusion as
`exponentialSurvivor_of_twoIncomm_sampled_differentiable`, with the
density hypothesis `TwoIncommensurablePeriodsGenerateDense a b`
replaced by `Irrational (a / b)`. -/
theorem exponentialSurvivor_of_twoIncomm_sampled_differentiable_irrational
    {DenseEnough : (ℕ → ℂ) → Prop}
    (hZD : ZeroDensityForcesZero DenseEnough)
    {Q : ℂ → ℂ}
    (hQ : FiniteExpType Q)
    (hQdiff : Differentiable ℂ Q)
    (hQnz : ∀ z : ℂ, Q z ≠ 0)
    (hext : LogDerivRealAxisConstExtendsGlobally Q)
    (hrecon : GlobalLogDerivConstForcesExponentialSurvivor Q)
    (I : TwoIncommensurableSampledWhoInputs Q DenseEnough)
    {a b : ℝ}
    (ha : I.inputs.input₁.a = (a : ℂ))
    (hb : I.inputs.input₂.a = (b : ℂ))
    (hA : I.inputs.input₁.A ≠ 0) (hB : I.inputs.input₂.A ≠ 0)
    (hirr : Irrational (a / b)) :
    ExponentialSurvivor Q :=
  exponentialSurvivor_of_twoIncomm_sampled_differentiable
    hZD hQ hQdiff hQnz hext hrecon I ha hb hA hB
    (twoIncommensurablePeriodsGenerateDense_of_irrational_div hirr)

/-- **Final pipeline → Q ≡ 1, with irrational ratio.** Same
conclusion as `where_rigidity_of_twoIncomm_sampled_differentiable`,
with the Kronecker density predicate replaced by `Irrational (a / b)`. -/
theorem where_rigidity_of_twoIncomm_sampled_differentiable_irrational
    {DenseEnough : (ℕ → ℂ) → Prop}
    (hZD : ZeroDensityForcesZero DenseEnough)
    {Q : ℂ → ℂ}
    (hQ : FiniteExpType Q)
    (hQdiff : Differentiable ℂ Q)
    (hQnz : ∀ z : ℂ, Q z ≠ 0)
    (hext : LogDerivRealAxisConstExtendsGlobally Q)
    (hrecon : GlobalLogDerivConstForcesExponentialSurvivor Q)
    (hKill : WhereKillsExponential Q)
    (hWhere : InfiniteWhere Q)
    (I : TwoIncommensurableSampledWhoInputs Q DenseEnough)
    {a b : ℝ}
    (ha : I.inputs.input₁.a = (a : ℂ))
    (hb : I.inputs.input₂.a = (b : ℂ))
    (hA : I.inputs.input₁.A ≠ 0) (hB : I.inputs.input₂.A ≠ 0)
    (hirr : Irrational (a / b)) :
    Q = fun _ : ℂ => 1 :=
  where_rigidity_of_twoIncomm_sampled_differentiable
    hZD hQ hQdiff hQnz hext hrecon hKill hWhere
    I ha hb hA hB
    (twoIncommensurablePeriodsGenerateDense_of_irrational_div hirr)

end GaussianWhoWhere
