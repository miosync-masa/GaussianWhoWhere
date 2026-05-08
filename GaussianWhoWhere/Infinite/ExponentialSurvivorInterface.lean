import GaussianWhoWhere.Infinite.TwoShiftCoupler

/-!
# Exponential survivor interface (Infinite L3)

We isolate the analytic step

  *two incommensurable global translation eigen-relations*  ⇒
  *Q(z) = exp(c · z)* for some constant `c : ℂ`,

as an abstract `Prop`-valued principle. The intended analytic proof
(showing that `Q′ / Q` has two incommensurable real periods and is
therefore constant) is **not** formalized here.

This file routes the principle from the previously installed
`TwoIncommensurableGlobalTranslationEigen` and the upstream sampled
who-inputs, to deliver the exponential survivor required by the
abstract Bridge C coupler.
-/

noncomputable section

namespace GaussianWhoWhere

/-- The **exponential survivor** statement: `Q(z) = exp(c · z)` for
some constant `c : ℂ`. This is the remaining degree of freedom after
the infinite Who condition has been globalized. -/
abbrev ExponentialSurvivor (Q : ℂ → ℂ) : Prop :=
  ∃ c : ℂ, Q = fun z : ℂ => Complex.exp (c * z)

/-- Abstract analytic principle: two incommensurable global
translation eigen-relations force an exponential survivor.

In the intended analytic proof, `Q′ / Q` is shown to have two
incommensurable real periods and to therefore be constant. We isolate
the conclusion as a `Prop`-valued bundle. -/
structure ExponentialSurvivorPrinciple (Q : ℂ → ℂ) : Prop where
  survivor :
    TwoIncommensurableGlobalTranslationEigen Q →
      ExponentialSurvivor Q

/-- Apply the exponential survivor principle to two incommensurable
global translation eigen-relations. -/
theorem exponential_survivor_of_two_global_translations
    {Q : ℂ → ℂ}
    (hExp : ExponentialSurvivorPrinciple Q)
    (hGlobal : TwoIncommensurableGlobalTranslationEigen Q) :
    ExponentialSurvivor Q :=
  hExp.survivor hGlobal

/-- **Composed input theorem.** From two incommensurable sampled
who-inputs, finite exponential type, a zero-density uniqueness
principle, and the exponential survivor principle, obtain the
exponential survivor. The pipeline:

  sampled who-inputs
    →[zero-density + finite-type]
  global incommensurable translation eigen-relations
    →[exponential survivor principle]
  Q(z) = exp(c · z)

is exactly the analytic input form consumed by
`TwoTranslationExponentialRigidity` in `InfiniteCoupler.lean`. -/
theorem exponential_survivor_of_two_sampled_who_inputs
    {DenseEnough : (ℕ → ℂ) → Prop}
    (hZD : ZeroDensityForcesZero DenseEnough)
    {Q : ℂ → ℂ} (hQ : FiniteExpType Q)
    (hExp : ExponentialSurvivorPrinciple Q)
    (I : TwoIncommensurableSampledWhoInputs Q DenseEnough) :
    ExponentialSurvivor Q :=
  hExp.survivor (I.toGlobal hZD hQ)

end GaussianWhoWhere
