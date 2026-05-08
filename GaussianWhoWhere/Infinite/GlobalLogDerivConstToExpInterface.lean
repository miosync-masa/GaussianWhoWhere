import GaussianWhoWhere.Infinite.RealAxisConstToGlobalInterface
import GaussianWhoWhere.Infinite.ExponentialSurvivorInterface
import GaussianWhoWhere.Infinite.WhereKillsExponential

/-!
# Global log-derivative constant → exponential survivor interface
(Infinite L3)

Packages the *analytic reconstruction* step

  `GloballyConstant (complexLogDeriv Q)  ⇒  ExponentialSurvivor Q`

as an interface predicate
`GlobalLogDerivConstForcesExponentialSurvivor Q`. The intended
analytic content (integrate the constant log-derivative `c` to recover
`Q(z) = exp(c · z) · Q(0)` and then normalize) is **not** undertaken
here.

We then route the previously installed sampled-input pipeline through
this interface to deliver the exponential survivor end-to-end, and
extend the route by one further step (consuming `InfiniteWhere Q` and
`WhereKillsExponential Q`) to deliver `Q ≡ 1`.
-/

noncomputable section

namespace GaussianWhoWhere

/-- **Reconstruction interface.** A globally constant log-derivative
yields an exponential survivor. -/
def GlobalLogDerivConstForcesExponentialSurvivor (Q : ℂ → ℂ) : Prop :=
  GloballyConstant (complexLogDeriv Q) → ExponentialSurvivor Q

/-- Apply the reconstruction interface. -/
theorem exponentialSurvivor_of_globalLogDerivConst
    {Q : ℂ → ℂ}
    (hrecon : GlobalLogDerivConstForcesExponentialSurvivor Q)
    (hconst : GloballyConstant (complexLogDeriv Q)) :
    ExponentialSurvivor Q :=
  hrecon hconst

/-- **Sampled-input pipeline → exponential survivor.** Combines the
real-axis-constant-to-global step
(`globallyConstant_complexLogDeriv_of_twoIncomm_sampled_differentiable`)
with the reconstruction interface. -/
theorem exponentialSurvivor_of_twoIncomm_sampled_differentiable
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
    (hgen : TwoIncommensurablePeriodsGenerateDense a b) :
    ExponentialSurvivor Q :=
  exponentialSurvivor_of_globalLogDerivConst hrecon
    (globallyConstant_complexLogDeriv_of_twoIncomm_sampled_differentiable
      hZD hQ hQdiff hQnz hext I ha hb hA hB hgen)

/-- **Final pipeline reaching `Q ≡ 1`.** Adds `InfiniteWhere Q` and
the existing `WhereKillsExponential Q` interface to the previous
exponential-survivor pipeline, dispatching through the
`one_of_where_and_exponential_survivor` adapter declared in
`Infinite/WhereKillsExponential.lean`. -/
theorem where_rigidity_of_twoIncomm_sampled_differentiable
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
    (hgen : TwoIncommensurablePeriodsGenerateDense a b) :
    Q = fun _ : ℂ => 1 :=
  one_of_where_and_exponential_survivor hKill hWhere
    (exponentialSurvivor_of_twoIncomm_sampled_differentiable
      hZD hQ hQdiff hQnz hext hrecon I ha hb hA hB hgen)

end GaussianWhoWhere
