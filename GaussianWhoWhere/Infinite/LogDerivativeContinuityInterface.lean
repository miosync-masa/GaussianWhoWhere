import GaussianWhoWhere.Infinite.TranslationEigenDeriv

/-!
# Log-derivative continuity interface (Infinite L3)

Isolates the remaining hypothesis

  `Continuous (RealRestrict (complexLogDeriv Q))`

as a named predicate `LogDerivContinuousOnReal Q`, and packages the
final C3 real-axis constancy theorems consuming only:

* nonvanishing of `Q`,
* nonzero eigenvalues `A, B`,
* two real translation eigen-relations on `Q`,
* the continuity interface,
* a dense-span hypothesis (or the arithmetic predicate
  `TwoIncommensurablePeriodsGenerateDense`).

The continuity content (typically obtained from `Q` holomorphic and
nonvanishing) is left as a future internalization target.
-/

noncomputable section

namespace GaussianWhoWhere

/-- **Continuity interface.** Marker predicate that the real
restriction of the candidate log-derivative is continuous. -/
def LogDerivContinuousOnReal (Q : ℂ → ℂ) : Prop :=
  Continuous (RealRestrict (complexLogDeriv Q))

/-- Unfolding lemma. -/
theorem continuous_realRestrict_complexLogDeriv
    {Q : ℂ → ℂ}
    (hcont : LogDerivContinuousOnReal Q) :
    Continuous (RealRestrict (complexLogDeriv Q)) :=
  hcont

/-- **Final C3 real-axis constancy, dense-span form.** Consumes the
continuity interface plus the algebraic data alone; no separate
derivative-eigen hypothesis is required. -/
theorem complexLogDeriv_const_on_real_of_two_eigen_denseSpan
    {Q : ℂ → ℂ} {a b : ℝ} {A B : ℂ}
    (hLcont : LogDerivContinuousOnReal Q)
    (hQnz : ∀ z : ℂ, Q z ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0)
    (heig_a : RealTranslationEigen Q a A)
    (heig_b : RealTranslationEigen Q b B)
    (hdense : Dense (IntegerPeriodSpan a b)) :
    ∀ x y : ℝ, complexLogDeriv Q (x : ℂ) = complexLogDeriv Q (y : ℂ) :=
  complexLogDeriv_const_on_real_of_two_realTranslationEigen_noDerivHyp_denseSpan
    (continuous_realRestrict_complexLogDeriv hLcont)
    hQnz hA hB heig_a heig_b hdense

/-- **Final C3 real-axis constancy, arithmetic-density form.** Same
conclusion consuming the existing predicate
`TwoIncommensurablePeriodsGenerateDense`. -/
theorem complexLogDeriv_const_on_real_of_two_eigen
    {Q : ℂ → ℂ} {a b : ℝ} {A B : ℂ}
    (hLcont : LogDerivContinuousOnReal Q)
    (hQnz : ∀ z : ℂ, Q z ≠ 0)
    (hA : A ≠ 0) (hB : B ≠ 0)
    (heig_a : RealTranslationEigen Q a A)
    (heig_b : RealTranslationEigen Q b B)
    (hgen : TwoIncommensurablePeriodsGenerateDense a b) :
    ∀ x y : ℝ, complexLogDeriv Q (x : ℂ) = complexLogDeriv Q (y : ℂ) :=
  complexLogDeriv_const_on_real_of_two_realTranslationEigen_noDerivHyp
    (continuous_realRestrict_complexLogDeriv hLcont)
    hQnz hA hB heig_a heig_b hgen

end GaussianWhoWhere
