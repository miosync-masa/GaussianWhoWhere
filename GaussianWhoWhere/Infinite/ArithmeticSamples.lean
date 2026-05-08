import GaussianWhoWhere.Infinite.ZeroDensityInterface

/-!
# Arithmetic samples — sampled translation relations (Infinite L3, Who side)

We do **not** introduce `Real.log` or `Nat.Coprime` here. The Who-side
analytic input is abstracted as a sampled translation relation:

  `Q(u n + a) = A · Q(u n)`   for every `n : ℕ`.

In the intended arithmetic application this comes from coprime
multiplicativity of the underlying Dirichlet-style function with
`a = log p`, `A = Q(log p)`, `u n = log m_n` over the integers `m_n`
coprime to `p`.

The single mechanical content here is:

* a sampled translation relation is exactly a `SampledZeros`-style
  vanishing of the translation defect, and
* therefore, under a zero-density principle and finite exponential
  type, it lifts to the *global* translation eigen-relation
  `Q(z + a) = A · Q(z)` consumed by the abstract Bridge C coupler.

We package the result both pointwise and as a small `SampledWhoInput`
bundle to support the upcoming two-shift composition (one input each
for `p = 2` and `p = 3`).
-/

noncomputable section

namespace GaussianWhoWhere

/-- A **sampled translation relation**: on the sampled sequence `u`,
the function `Q` satisfies `Q(u n + a) = A · Q(u n)` for every `n`.

In the intended arithmetic application `a = log p`, `A = Q(log p)`,
and `u n = log m_n` with `m_n` coprime to `p`. -/
def SampledTranslationRelation
    (Q : ℂ → ℂ) (a A : ℂ) (u : ℕ → ℂ) : Prop :=
  ∀ n : ℕ, Q (u n + a) = A * Q (u n)

/-- A sampled translation relation is exactly the statement that the
translation defect vanishes on the sampled sequence. -/
theorem sampledZeros_translationDefect_of_sampledTranslationRelation
    {Q : ℂ → ℂ} {a A : ℂ} {u : ℕ → ℂ}
    (hrel : SampledTranslationRelation Q a A u) :
    SampledZeros (translationDefect Q a A) u := by
  intro n
  unfold translationDefect
  unfold SampledTranslationRelation at hrel
  rw [hrel n]
  simp

/-- **Combined Who-side input theorem.** A sampled translation
relation, together with finite exponential type and a zero-density
uniqueness principle, lifts to the global translation eigen-relation

  `Q(z + a) = A · Q(z)`   for every `z : ℂ`,

which is exactly the input form consumed by the abstract Bridge C
coupler in `InfiniteCoupler.lean`. -/
theorem translation_eigen_of_sampledTranslationRelation
    {DenseEnough : (ℕ → ℂ) → Prop}
    (hZD : ZeroDensityForcesZero DenseEnough)
    {Q : ℂ → ℂ} (hQ : FiniteExpType Q)
    (a A : ℂ) {u : ℕ → ℂ}
    (hu : DenseEnough u)
    (hrel : SampledTranslationRelation Q a A u) :
    ∀ z : ℂ, Q (z + a) = A * Q z :=
  translation_eigen_of_sampledZeros
    hZD hQ a A hu
    (sampledZeros_translationDefect_of_sampledTranslationRelation hrel)

/-! ## Packaged who-input bundle

A small data-carrying bundle for one arithmetic shift. Two such bundles
(one for `p = 2`, one for `p = 3`) compose into the `InfiniteWho`
record needed by the Bridge C coupler. -/

/-- A packaged sampled who-input for a single arithmetic shift:
the shift `a`, eigenvalue `A`, the sample sequence `u`, the density
proof, and the sampled translation relation. -/
structure SampledWhoInput
    (Q : ℂ → ℂ) (DenseEnough : (ℕ → ℂ) → Prop) where
  a : ℂ
  A : ℂ
  u : ℕ → ℂ
  dense : DenseEnough u
  relation : SampledTranslationRelation Q a A u

/-- A packaged sampled who-input yields the global translation
eigen-relation. -/
theorem SampledWhoInput.translation_eigen
    {DenseEnough : (ℕ → ℂ) → Prop}
    (hZD : ZeroDensityForcesZero DenseEnough)
    {Q : ℂ → ℂ} (hQ : FiniteExpType Q)
    (I : SampledWhoInput Q DenseEnough) :
    ∀ z : ℂ, Q (z + I.a) = I.A * Q z :=
  translation_eigen_of_sampledTranslationRelation
    hZD hQ I.a I.A I.dense I.relation

end GaussianWhoWhere
