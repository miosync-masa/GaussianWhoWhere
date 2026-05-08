import GaussianWhoWhere.Infinite.KroneckerPipeline
import GaussianWhoWhere.Infinite.WhereKillsExponentialConcrete

/-!
# Function-level → exponent-level Where lift (Infinite L3)

Decomposes the abstract `WhereKillsExponential Q` interface into:

1. the *function-level → exponent-level* lift (a Prop-valued
   predicate `FunctionWhereForcesExponentReflection Q`), and
2. the already-internalized *exponent-level core*
   `whereKillsExponentLevel`
   (from `Infinite/WhereKillsExponentialConcrete.lean`).

The lift component is the genuinely analytic step; once it is
supplied, the rest of `WhereKillsExponential Q` follows mechanically
from the exponent-level core. This sharpens the C3 pipeline so the
final theorem accepts the lift directly, eliminating
`WhereKillsExponential` as an analytic interface.
-/

noncomputable section

namespace GaussianWhoWhere

/-- **Function-level → exponent-level lift.** Function-level Where
symmetry, together with an exponential-survivor form for `Q`, yields
exponent-level reflection for the exponent constant `c`.

This is the genuinely analytic step (it relies on injectivity /
periodicity properties of the complex exponential). We isolate it as
a Prop-valued interface; the rest of `WhereKillsExponential` reduces
to it. -/
def FunctionWhereForcesExponentReflection (Q : ℂ → ℂ) : Prop :=
  InfiniteWhere Q →
    ∀ c : ℂ,
      Q = (fun z : ℂ => Complex.exp (c * z)) →
      ExponentReflection c

/-- The function-level-to-exponent-level lift plus the
already-internalized exponent-level core
(`whereKillsExponentLevel`) yields the
existing `WhereKillsExponential` interface. -/
theorem whereKillsExponential_of_functionWhereForcesExponentReflection
    {Q : ℂ → ℂ}
    (hlift : FunctionWhereForcesExponentReflection Q) :
    WhereKillsExponential Q := by
  refine ⟨?_⟩
  intro hWhere c hExp
  exact whereKillsExponentLevel hExp (hlift hWhere c hExp)

/-- **Final pipeline → Q ≡ 1, with the function-level lift in place
of `WhereKillsExponential`.** -/
theorem where_rigidity_of_twoIncomm_sampled_differentiable_irrational_exponentLift
    {DenseEnough : (ℕ → ℂ) → Prop}
    (hZD : ZeroDensityForcesZero DenseEnough)
    {Q : ℂ → ℂ}
    (hQ : FiniteExpType Q)
    (hQdiff : Differentiable ℂ Q)
    (hQnz : ∀ z : ℂ, Q z ≠ 0)
    (hext : LogDerivRealAxisConstExtendsGlobally Q)
    (hrecon : GlobalLogDerivConstForcesExponentialSurvivor Q)
    (hlift : FunctionWhereForcesExponentReflection Q)
    (hWhere : InfiniteWhere Q)
    (I : TwoIncommensurableSampledWhoInputs Q DenseEnough)
    {a b : ℝ}
    (ha : I.inputs.input₁.a = (a : ℂ))
    (hb : I.inputs.input₂.a = (b : ℂ))
    (hA : I.inputs.input₁.A ≠ 0) (hB : I.inputs.input₂.A ≠ 0)
    (hirr : Irrational (a / b)) :
    Q = fun _ : ℂ => 1 :=
  where_rigidity_of_twoIncomm_sampled_differentiable_irrational
    hZD hQ hQdiff hQnz hext hrecon
    (whereKillsExponential_of_functionWhereForcesExponentReflection hlift)
    hWhere I ha hb hA hB hirr

end GaussianWhoWhere
