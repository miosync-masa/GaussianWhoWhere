import GaussianWhoWhere.Infinite.WhereKillsExponential

/-!
# Top-level infinite rigidity (Infinite L3 DAG)

This file does **not** prove any new mathematics. It packages the
already-installed Infinite L3 interface layers into a single top-level
theorem DAG:

  `FiniteExpType Q`
  `+ ZeroDensityForcesZero`
  `+ TwoIncommensurableSampledWhoInputs`
  `+ ExponentialSurvivorPrinciple`
  `+ InfiniteWhere`
  `+ WhereKillsExponential`
  `⇒ Q ≡ 1`.

Jensen / Cartwright / zero-density / exponential-survivor analytic
content remains isolated inside the corresponding `Prop`-valued
inputs; this file is the logical coupler skeleton, no analytic theorem
is proved here.
-/

noncomputable section

namespace GaussianWhoWhere

/-- **Infinite HP-style who/where rigidity, sampled-input version.**

Composes the full interface-level infinite DAG:

1. finite exponential type keeps translation defects inside the
   admissible analytic class;
2. zero-density uniqueness lifts sampled translation relations to
   global translation eigen-relations;
3. two incommensurable global translations leave only an exponential
   survivor `Q(z) = exp(c · z)`;
4. the where symmetry kills the exponential survivor.

No Jensen/Cartwright theorem is proved here; those analytic inputs
are isolated in `ZeroDensityForcesZero`,
`ExponentialSurvivorPrinciple`, and `WhereKillsExponential`. -/
theorem infinite_rigidity_from_sampled_who_where
    {DenseEnough : (ℕ → ℂ) → Prop}
    (hZD : ZeroDensityForcesZero DenseEnough)
    {Q : ℂ → ℂ}
    (hQ : FiniteExpType Q)
    (hExp : ExponentialSurvivorPrinciple Q)
    (hKill : WhereKillsExponential Q)
    (hWhere : InfiniteWhere Q)
    (I : TwoIncommensurableSampledWhoInputs Q DenseEnough) :
    Q = fun _ : ℂ => 1 :=
  infinite_who_where_rigidity_from_sampled_inputs
    hZD hQ hExp hKill hWhere I

/-- **Infinite HP-style who/where rigidity, global-translation version.**

This variant starts after the zero-density step has already lifted the
sampled arithmetic relations to two incommensurable global translation
eigen-relations. -/
theorem infinite_rigidity_from_global_who_where
    {Q : ℂ → ℂ}
    (hExp : ExponentialSurvivorPrinciple Q)
    (hKill : WhereKillsExponential Q)
    (hWhere : InfiniteWhere Q)
    (G : TwoIncommensurableGlobalTranslationEigen Q) :
    Q = fun _ : ℂ => 1 :=
  infinite_who_where_rigidity_from_global_translations
    hExp hKill hWhere G

/-- Interpretation-flavored alias of the sampled-input theorem
emphasizing the Bridge C reading: the infinite who/where coupler
collapses the survivor to the Gaussian normalization, represented here
by the constant-one deformation factor. -/
theorem bridgeC_infinite_coupler
    {DenseEnough : (ℕ → ℂ) → Prop}
    (hZD : ZeroDensityForcesZero DenseEnough)
    {Q : ℂ → ℂ}
    (hQ : FiniteExpType Q)
    (hExp : ExponentialSurvivorPrinciple Q)
    (hKill : WhereKillsExponential Q)
    (hWhere : InfiniteWhere Q)
    (I : TwoIncommensurableSampledWhoInputs Q DenseEnough) :
    Q = fun _ : ℂ => 1 :=
  infinite_rigidity_from_sampled_who_where
    hZD hQ hExp hKill hWhere I

end GaussianWhoWhere
