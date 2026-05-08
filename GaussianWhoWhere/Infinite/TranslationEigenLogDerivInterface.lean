import GaussianWhoWhere.Infinite.ExponentialSurvivorConcrete

/-!
# Translation eigen → log-derivative period interface (Infinite L3)

We do **not** define `deriv`, `Q'/Q`, or any analytic derivative
content at this layer. The single mechanical purpose is to install a
named interface

  `LogDerivRespectsRealTranslationEigen Q L a A`

that records the *future* analytic theorem

  `Q(z + a) = A · Q(z)  ⇒  L(z + a) = L(z)`

in a Prop-valued shape, and to compose the interface with the
already-installed log-derivative coupler. Two such interface
hypotheses (one for each shift) plus continuity of the real
restriction of `L` and a density hypothesis dispatch through
`logDeriv_two_periods_force_const_on_real`.
-/

noncomputable section

namespace GaussianWhoWhere

/-- A real shift `a : ℝ` is a translation eigen-direction of `Q`
with eigenvalue `A : ℂ`. -/
def RealTranslationEigen (Q : ℂ → ℂ) (a : ℝ) (A : ℂ) : Prop :=
  ∀ z : ℂ, Q (z + (a : ℂ)) = A * Q z

/-- Interface predicate: a translation eigen-relation of `Q` along
the real shift `a` propagates to a complex-level real period of the
candidate log-derivative `L`.

This is the named hypothesis the future analytic argument will
deliver (once `L = Q'/Q` is defined and the chain rule + the
eigen-relation are combined). At this layer we keep it as a
predicate hook and route it through the existing coupler. -/
def LogDerivRespectsRealTranslationEigen
    (Q L : ℂ → ℂ) (a : ℝ) (A : ℂ) : Prop :=
  RealTranslationEigen Q a A → LogDerivHasComplexRealPeriod Q L a

/-- Apply the interface predicate. -/
theorem logDeriv_period_of_realTranslationEigen
    {Q L : ℂ → ℂ} {a : ℝ} {A : ℂ}
    (hrespect : LogDerivRespectsRealTranslationEigen Q L a A)
    (heig : RealTranslationEigen Q a A) :
    LogDerivHasComplexRealPeriod Q L a :=
  hrespect heig

/-- **Constancy on the real line from two translation eigen-relations,
dense-span form.** -/
theorem logDeriv_const_on_real_of_two_realTranslationEigen_denseSpan
    {Q L : ℂ → ℂ} {a b : ℝ} {A B : ℂ}
    (hLcont : Continuous (RealRestrict L))
    (hrespect_a : LogDerivRespectsRealTranslationEigen Q L a A)
    (hrespect_b : LogDerivRespectsRealTranslationEigen Q L b B)
    (heig_a : RealTranslationEigen Q a A)
    (heig_b : RealTranslationEigen Q b B)
    (hdense : Dense (IntegerPeriodSpan a b)) :
    ∀ x y : ℝ, L (x : ℂ) = L (y : ℂ) :=
  logDeriv_two_periods_force_const_on_real
    hLcont
    (logDeriv_period_of_realTranslationEigen hrespect_a heig_a)
    (logDeriv_period_of_realTranslationEigen hrespect_b heig_b)
    hdense

/-- **Constancy on the real line from two translation eigen-relations,
arithmetic-density form.** Consumes the existing predicate
`TwoIncommensurablePeriodsGenerateDense`. -/
theorem logDeriv_const_on_real_of_two_realTranslationEigen
    {Q L : ℂ → ℂ} {a b : ℝ} {A B : ℂ}
    (hLcont : Continuous (RealRestrict L))
    (hrespect_a : LogDerivRespectsRealTranslationEigen Q L a A)
    (hrespect_b : LogDerivRespectsRealTranslationEigen Q L b B)
    (heig_a : RealTranslationEigen Q a A)
    (heig_b : RealTranslationEigen Q b B)
    (hgen : TwoIncommensurablePeriodsGenerateDense a b) :
    ∀ x y : ℝ, L (x : ℂ) = L (y : ℂ) :=
  logDeriv_two_incommensurable_periods_force_const_on_real
    hLcont
    (logDeriv_period_of_realTranslationEigen hrespect_a heig_a)
    (logDeriv_period_of_realTranslationEigen hrespect_b heig_b)
    hgen

end GaussianWhoWhere
