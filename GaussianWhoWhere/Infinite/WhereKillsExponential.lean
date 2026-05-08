import GaussianWhoWhere.InfiniteCoupler
import GaussianWhoWhere.Infinite.ExponentialSurvivorInterface

/-!
# Where kills exponential survivor — pipeline composition (Infinite L3)

This file does **not** re-introduce `InfiniteWhere` or
`WhereKillsExponential`; both are already declared in
`InfiniteCoupler.lean` at the abstract Bridge C layer. We instead
provide:

* a thin `ExponentialSurvivor`-flavored adapter
  (`one_of_where_and_exponential_survivor`) that consumes
  `WhereKillsExponential.kill` plus an
  `ExponentialSurvivor` witness, and
* the two end-to-end pipeline theorems
  (`infinite_who_where_rigidity_from_sampled_inputs`,
  `infinite_who_where_rigidity_from_global_translations`) that
  compose every L3 layer down to `Q ≡ 1`.

These are the application-level theorems intended for downstream use.
-/

noncomputable section

namespace GaussianWhoWhere

/-- Apply the where-kills-exponential principle in
`ExponentialSurvivor`-flavored form: from a where-symmetric `Q` and
an exponential survivor witness, conclude `Q ≡ 1`. -/
theorem one_of_where_and_exponential_survivor
    {Q : ℂ → ℂ}
    (hKill : WhereKillsExponential Q)
    (hWhere : InfiniteWhere Q)
    (hSurv : ExponentialSurvivor Q) :
    Q = fun _ : ℂ => 1 := by
  obtain ⟨c, hQexp⟩ := hSurv
  exact hKill.kill hWhere c hQexp

/-- **Sampled-input pipeline.** Compose every L3 layer end-to-end:

  sampled who-inputs (incommensurable shifts)
    →[zero-density + finite-type]
  global incommensurable translation eigen-relations
    →[exponential survivor principle]
  exponential survivor `Q(z) = exp(c · z)`
    →[where kills exponential]
  `Q ≡ 1`. -/
theorem infinite_who_where_rigidity_from_sampled_inputs
    {DenseEnough : (ℕ → ℂ) → Prop}
    (hZD : ZeroDensityForcesZero DenseEnough)
    {Q : ℂ → ℂ} (hQ : FiniteExpType Q)
    (hExp : ExponentialSurvivorPrinciple Q)
    (hKill : WhereKillsExponential Q)
    (hWhere : InfiniteWhere Q)
    (I : TwoIncommensurableSampledWhoInputs Q DenseEnough) :
    Q = fun _ : ℂ => 1 :=
  one_of_where_and_exponential_survivor hKill hWhere
    (exponential_survivor_of_two_sampled_who_inputs hZD hQ hExp I)

/-- **Global-translation pipeline.** Variant starting after the
zero-density step has already lifted the sampled relations to global
incommensurable translations. -/
theorem infinite_who_where_rigidity_from_global_translations
    {Q : ℂ → ℂ}
    (hExp : ExponentialSurvivorPrinciple Q)
    (hKill : WhereKillsExponential Q)
    (hWhere : InfiniteWhere Q)
    (G : TwoIncommensurableGlobalTranslationEigen Q) :
    Q = fun _ : ℂ => 1 :=
  one_of_where_and_exponential_survivor hKill hWhere
    (exponential_survivor_of_two_global_translations hExp G)

end GaussianWhoWhere
