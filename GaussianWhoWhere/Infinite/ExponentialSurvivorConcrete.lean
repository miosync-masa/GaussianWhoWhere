import GaussianWhoWhere.Infinite.LogDerivativeCoupler
import GaussianWhoWhere.Infinite.TranslationZeros
import GaussianWhoWhere.Infinite.ExponentialSurvivorInterface

/-!
# Exponential survivor concrete scaffolding (Infinite L3)

Packages the route

  two translation eigen relations
    → log-derivative has two real periods
    → dense-period coupler forces log-derivative constant on real axis
    → exponential survivor interface

at the *naming* level, without yet introducing analytic derivative
content. The new top-level theorems consume hypotheses about a
candidate log-derivative `L : ℂ → ℂ` (continuity of its real
restriction, two real-shift periodicities, and a density predicate)
and dispatch them through the previously installed
`LogDerivativeCoupler`.

The concrete log-derivative arguments — definition of `L = Q'/Q`,
nonvanishing of `Q`, and the derivation of the periodicity of `L`
from the translation eigen-relations on `Q` — remain future work.
This file establishes the named hypothesis pattern those arguments
will eventually be slotted into.
-/

/- The `Q` arguments below are intentional naming hooks recording the
intended source of each hypothesis (the eventual `L = Q'/Q`); they do
not appear in the right-hand sides at this layer, so we silence the
unused-variable linter for this file only. -/
set_option linter.unusedVariables false

noncomputable section

namespace GaussianWhoWhere

/-- A real shift `a` is a complex-level real period of a candidate
log-derivative `L`. This is the same Prop as `ComplexRealPeriod L a`;
the alias name records the intended source (the eventual `L = Q'/Q`)
and links the hypothesis to the eigen-related function `Q`. -/
def LogDerivHasComplexRealPeriod
    (Q L : ℂ → ℂ) (a : ℝ) : Prop :=
  ComplexRealPeriod L a

/-- A placeholder predicate marking `L` as the intended log-derivative
candidate of `Q`. Trivial at this layer; concrete analytic content
will be supplied later. -/
def LogDerivCandidate (_Q _L : ℂ → ℂ) : Prop :=
  True

/-- **Constancy on the real line from two log-derivative periods.** -/
theorem logDeriv_two_periods_force_const_on_real
    {Q L : ℂ → ℂ} {a b : ℝ}
    (hLcont : Continuous (RealRestrict L))
    (ha : LogDerivHasComplexRealPeriod Q L a)
    (hb : LogDerivHasComplexRealPeriod Q L b)
    (hdense : Dense (IntegerPeriodSpan a b)) :
    ∀ x y : ℝ, L (x : ℂ) = L (y : ℂ) :=
  two_complex_real_periods_dense_force_const_on_real
    hLcont ha hb hdense

/-- Specialized form consuming the existing arithmetic predicate
`TwoIncommensurablePeriodsGenerateDense`. -/
theorem logDeriv_two_incommensurable_periods_force_const_on_real
    {Q L : ℂ → ℂ} {a b : ℝ}
    (hLcont : Continuous (RealRestrict L))
    (ha : LogDerivHasComplexRealPeriod Q L a)
    (hb : LogDerivHasComplexRealPeriod Q L b)
    (hgen : TwoIncommensurablePeriodsGenerateDense a b) :
    ∀ x y : ℝ, L (x : ℂ) = L (y : ℂ) :=
  two_incommensurable_complex_real_periods_force_const_on_real
    hLcont ha hb hgen

/-- **Two-shift log-derivative constancy.** Top-level convenience
wrapper using the more direct `ComplexRealPeriod` hypothesis names
(without the `Q`-decoration), matching the form expected by future
analytic interfaces. -/
theorem two_shift_logDeriv_constant_on_real
    {Q L : ℂ → ℂ} {a b : ℝ}
    (hLcont : Continuous (RealRestrict L))
    (hperiod_a : ComplexRealPeriod L a)
    (hperiod_b : ComplexRealPeriod L b)
    (hgen : TwoIncommensurablePeriodsGenerateDense a b) :
    ∀ x y : ℝ, L (x : ℂ) = L (y : ℂ) :=
  two_incommensurable_complex_real_periods_force_const_on_real
    hLcont hperiod_a hperiod_b hgen

end GaussianWhoWhere
