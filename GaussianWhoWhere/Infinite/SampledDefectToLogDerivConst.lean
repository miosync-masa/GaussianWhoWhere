import GaussianWhoWhere.Infinite.TranslationDefectToEigenCoupler
import GaussianWhoWhere.Infinite.TwoShiftCoupler

/-!
# Sampled who-input → real-shift eigen → log-derivative constancy
(Infinite L3)

Routes a `SampledWhoInput` (or a pair of them) directly into the
candidate-log-derivative real-axis constancy theorems. The bridge

  `Q(z + I.a) = I.A · Q(z)` (global, via `SampledWhoInput.translation_eigen`)
    + `I.a = (t : ℂ)`
  ⇒ `RealTranslationEigen Q t I.A`

uses the `SampledWhoInput`-side `translation_eigen` already available
from `ArithmeticSamples.lean`. With this in hand, two such inputs
combine into the final C3 constancy theorem on the candidate
log-derivative.
-/

noncomputable section

namespace GaussianWhoWhere

/-- A sampled who-input whose shift `I.a` lifts a real number `t`
yields a real-translation eigen-relation with the same eigenvalue. -/
theorem realTranslationEigen_of_sampledWhoInput_realShift
    {DenseEnough : (ℕ → ℂ) → Prop}
    (hZD : ZeroDensityForcesZero DenseEnough)
    {Q : ℂ → ℂ}
    (hQ : FiniteExpType Q)
    (I : SampledWhoInput Q DenseEnough)
    {t : ℝ} (ht : I.a = (t : ℂ)) :
    RealTranslationEigen Q t I.A := by
  intro z
  have h := I.translation_eigen hZD hQ z
  -- h : Q (z + I.a) = I.A * Q z
  rw [ht] at h
  exact h

/-- **Real-axis constancy of the candidate log-derivative from two
sampled who-inputs whose shifts lift real numbers (dense-span form).** -/
theorem complexLogDeriv_const_on_real_of_two_sampledWhoInputs_realShift_denseSpan
    {DenseEnough : (ℕ → ℂ) → Prop}
    (hZD : ZeroDensityForcesZero DenseEnough)
    {Q : ℂ → ℂ}
    (hQ : FiniteExpType Q)
    (hLcont : LogDerivContinuousOnReal Q)
    (hQnz : ∀ z : ℂ, Q z ≠ 0)
    (I : TwoSampledWhoInputs Q DenseEnough)
    {a b : ℝ}
    (ha : I.input₁.a = (a : ℂ))
    (hb : I.input₂.a = (b : ℂ))
    (hA : I.input₁.A ≠ 0) (hB : I.input₂.A ≠ 0)
    (hdense : Dense (IntegerPeriodSpan a b)) :
    ∀ x y : ℝ, complexLogDeriv Q (x : ℂ) = complexLogDeriv Q (y : ℂ) := by
  have heig_a : RealTranslationEigen Q a I.input₁.A :=
    realTranslationEigen_of_sampledWhoInput_realShift hZD hQ I.input₁ ha
  have heig_b : RealTranslationEigen Q b I.input₂.A :=
    realTranslationEigen_of_sampledWhoInput_realShift hZD hQ I.input₂ hb
  exact complexLogDeriv_const_on_real_of_two_eigen_denseSpan
    hLcont hQnz hA hB heig_a heig_b hdense

/-- Same conclusion consuming `TwoIncommensurablePeriodsGenerateDense`. -/
theorem complexLogDeriv_const_on_real_of_two_sampledWhoInputs_realShift
    {DenseEnough : (ℕ → ℂ) → Prop}
    (hZD : ZeroDensityForcesZero DenseEnough)
    {Q : ℂ → ℂ}
    (hQ : FiniteExpType Q)
    (hLcont : LogDerivContinuousOnReal Q)
    (hQnz : ∀ z : ℂ, Q z ≠ 0)
    (I : TwoSampledWhoInputs Q DenseEnough)
    {a b : ℝ}
    (ha : I.input₁.a = (a : ℂ))
    (hb : I.input₂.a = (b : ℂ))
    (hA : I.input₁.A ≠ 0) (hB : I.input₂.A ≠ 0)
    (hgen : TwoIncommensurablePeriodsGenerateDense a b) :
    ∀ x y : ℝ, complexLogDeriv Q (x : ℂ) = complexLogDeriv Q (y : ℂ) := by
  have heig_a : RealTranslationEigen Q a I.input₁.A :=
    realTranslationEigen_of_sampledWhoInput_realShift hZD hQ I.input₁ ha
  have heig_b : RealTranslationEigen Q b I.input₂.A :=
    realTranslationEigen_of_sampledWhoInput_realShift hZD hQ I.input₂ hb
  exact complexLogDeriv_const_on_real_of_two_eigen
    hLcont hQnz hA hB heig_a heig_b hgen

end GaussianWhoWhere
