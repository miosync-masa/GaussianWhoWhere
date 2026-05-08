import GaussianWhoWhere.Infinite.ArithmeticSamples

/-!
# Two-shift coupler (Infinite L3)

Compose two `SampledWhoInput`s — intended to come from coprime
multiplicativity at two distinct primes (e.g. `p = 2` and `p = 3`) —
into a pair of global translation eigen-relations, with an
incommensurability witness on the shifts.

This is the data side that feeds the `InfiniteWho` structure consumed
by the abstract Bridge C coupler in `InfiniteCoupler.lean`.
-/

noncomputable section

namespace GaussianWhoWhere

/-- A packaged pair of sampled who-inputs. In the intended
application these correspond to two arithmetic shifts (e.g. `log 2`
and `log 3`). -/
structure TwoSampledWhoInputs
    (Q : ℂ → ℂ) (DenseEnough : (ℕ → ℂ) → Prop) where
  input₁ : SampledWhoInput Q DenseEnough
  input₂ : SampledWhoInput Q DenseEnough

/-- The first sampled who-input yields the first global translation
eigen-relation. -/
theorem TwoSampledWhoInputs.translation_eigen₁
    {DenseEnough : (ℕ → ℂ) → Prop}
    (hZD : ZeroDensityForcesZero DenseEnough)
    {Q : ℂ → ℂ} (hQ : FiniteExpType Q)
    (I : TwoSampledWhoInputs Q DenseEnough) :
    ∀ z : ℂ, Q (z + I.input₁.a) = I.input₁.A * Q z :=
  I.input₁.translation_eigen hZD hQ

/-- The second sampled who-input yields the second global translation
eigen-relation. -/
theorem TwoSampledWhoInputs.translation_eigen₂
    {DenseEnough : (ℕ → ℂ) → Prop}
    (hZD : ZeroDensityForcesZero DenseEnough)
    {Q : ℂ → ℂ} (hQ : FiniteExpType Q)
    (I : TwoSampledWhoInputs Q DenseEnough) :
    ∀ z : ℂ, Q (z + I.input₂.a) = I.input₂.A * Q z :=
  I.input₂.translation_eigen hZD hQ

/-- A pair of global translation eigen-relations, extracted from two
sampled who-inputs. -/
structure TwoGlobalTranslationEigen (Q : ℂ → ℂ) where
  a₁ : ℂ
  A₁ : ℂ
  a₂ : ℂ
  A₂ : ℂ
  trans₁ : ∀ z : ℂ, Q (z + a₁) = A₁ * Q z
  trans₂ : ∀ z : ℂ, Q (z + a₂) = A₂ * Q z

/-- Convert two sampled who-inputs into two global translation
eigen-relations. -/
def TwoSampledWhoInputs.toGlobalTranslationEigen
    {DenseEnough : (ℕ → ℂ) → Prop}
    (hZD : ZeroDensityForcesZero DenseEnough)
    {Q : ℂ → ℂ} (hQ : FiniteExpType Q)
    (I : TwoSampledWhoInputs Q DenseEnough) :
    TwoGlobalTranslationEigen Q :=
  { a₁ := I.input₁.a
    A₁ := I.input₁.A
    a₂ := I.input₂.a
    A₂ := I.input₂.A
    trans₁ := I.translation_eigen₁ hZD hQ
    trans₂ := I.translation_eigen₂ hZD hQ }

/-- Two sampled who-inputs with incommensurable shifts. -/
structure TwoIncommensurableSampledWhoInputs
    (Q : ℂ → ℂ) (DenseEnough : (ℕ → ℂ) → Prop) where
  inputs : TwoSampledWhoInputs Q DenseEnough
  incommensurable :
    ∀ q : ℚ, inputs.input₁.a ≠ (q : ℂ) * inputs.input₂.a

/-- Global translation eigen-relations with an incommensurability
witness. -/
structure TwoIncommensurableGlobalTranslationEigen (Q : ℂ → ℂ) where
  global : TwoGlobalTranslationEigen Q
  incommensurable :
    ∀ q : ℚ, global.a₁ ≠ (q : ℂ) * global.a₂

/-- Lift incommensurable sampled who-inputs to incommensurable global
translation eigen-relations. -/
def TwoIncommensurableSampledWhoInputs.toGlobal
    {DenseEnough : (ℕ → ℂ) → Prop}
    (hZD : ZeroDensityForcesZero DenseEnough)
    {Q : ℂ → ℂ} (hQ : FiniteExpType Q)
    (I : TwoIncommensurableSampledWhoInputs Q DenseEnough) :
    TwoIncommensurableGlobalTranslationEigen Q :=
  { global := I.inputs.toGlobalTranslationEigen hZD hQ
    incommensurable := I.incommensurable }

end GaussianWhoWhere
