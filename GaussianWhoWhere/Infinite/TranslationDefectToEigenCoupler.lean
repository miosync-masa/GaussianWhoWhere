import GaussianWhoWhere.Infinite.LogDerivativeContinuityInterface
import GaussianWhoWhere.Infinite.TranslationDefect

/-!
# Translation defect ↔ real translation eigen (Infinite L3)

Bridges the older translation-defect layer
(`Infinite/TranslationDefect.lean`) to the newer
real-translation-eigen / log-derivative backbone introduced in
`TranslationEigenLogDerivInterface` and downstream.

The single algebraic identity is

  `realLogShiftDefect Q t z = Q (z + (t : ℂ)) - Q (t : ℂ) · Q z`,

so the vanishing of `realLogShiftDefect Q t` on every `z : ℂ` is
exactly `RealTranslationEigen Q t (Q (t : ℂ))`.

We package both directions of this equivalence, then route a pair of
pointwise-zero defects (one per shift) into the previously installed
final C3 real-axis constancy theorems
(`complexLogDeriv_const_on_real_of_two_eigen_*`).
-/

noncomputable section

namespace GaussianWhoWhere

/-- A pointwise vanishing real-log-shift defect at shift `t` is
exactly the real translation eigen-relation with eigenvalue `Q(t)`. -/
theorem realTranslationEigen_of_realLogShiftDefect_eq_zero
    {Q : ℂ → ℂ} {t : ℝ}
    (hzero : ∀ z : ℂ, realLogShiftDefect Q t z = 0) :
    RealTranslationEigen Q t (Q (t : ℂ)) := by
  intro z
  have hz := hzero z
  unfold realLogShiftDefect translationDefect at hz
  exact sub_eq_zero.mp hz

/-- Conversely, the real translation eigen-relation at `(t, Q(t))`
yields a pointwise-vanishing real-log-shift defect. -/
theorem realLogShiftDefect_eq_zero_of_realTranslationEigen
    {Q : ℂ → ℂ} {t : ℝ}
    (heig : RealTranslationEigen Q t (Q (t : ℂ))) :
    ∀ z : ℂ, realLogShiftDefect Q t z = 0 := by
  intro z
  unfold realLogShiftDefect translationDefect
  rw [heig z]
  ring

/-- **Real-axis constancy of the candidate log-derivative from two
vanishing real-log-shift defects (dense-span form).** Combines the
defect ⇒ eigen bridge with
`complexLogDeriv_const_on_real_of_two_eigen_denseSpan`. -/
theorem complexLogDeriv_const_on_real_of_two_realLogShiftDefects_denseSpan
    {Q : ℂ → ℂ} {a b : ℝ}
    (hLcont : LogDerivContinuousOnReal Q)
    (hQnz : ∀ z : ℂ, Q z ≠ 0)
    (hzero_a : ∀ z : ℂ, realLogShiftDefect Q a z = 0)
    (hzero_b : ∀ z : ℂ, realLogShiftDefect Q b z = 0)
    (hdense : Dense (IntegerPeriodSpan a b)) :
    ∀ x y : ℝ, complexLogDeriv Q (x : ℂ) = complexLogDeriv Q (y : ℂ) := by
  have heig_a : RealTranslationEigen Q a (Q (a : ℂ)) :=
    realTranslationEigen_of_realLogShiftDefect_eq_zero hzero_a
  have heig_b : RealTranslationEigen Q b (Q (b : ℂ)) :=
    realTranslationEigen_of_realLogShiftDefect_eq_zero hzero_b
  exact complexLogDeriv_const_on_real_of_two_eigen_denseSpan
    hLcont hQnz
    (hQnz (a : ℂ)) (hQnz (b : ℂ))
    heig_a heig_b hdense

/-- Same conclusion consuming `TwoIncommensurablePeriodsGenerateDense`. -/
theorem complexLogDeriv_const_on_real_of_two_realLogShiftDefects
    {Q : ℂ → ℂ} {a b : ℝ}
    (hLcont : LogDerivContinuousOnReal Q)
    (hQnz : ∀ z : ℂ, Q z ≠ 0)
    (hzero_a : ∀ z : ℂ, realLogShiftDefect Q a z = 0)
    (hzero_b : ∀ z : ℂ, realLogShiftDefect Q b z = 0)
    (hgen : TwoIncommensurablePeriodsGenerateDense a b) :
    ∀ x y : ℝ, complexLogDeriv Q (x : ℂ) = complexLogDeriv Q (y : ℂ) := by
  have heig_a : RealTranslationEigen Q a (Q (a : ℂ)) :=
    realTranslationEigen_of_realLogShiftDefect_eq_zero hzero_a
  have heig_b : RealTranslationEigen Q b (Q (b : ℂ)) :=
    realTranslationEigen_of_realLogShiftDefect_eq_zero hzero_b
  exact complexLogDeriv_const_on_real_of_two_eigen
    hLcont hQnz
    (hQnz (a : ℂ)) (hQnz (b : ℂ))
    heig_a heig_b hgen

end GaussianWhoWhere
