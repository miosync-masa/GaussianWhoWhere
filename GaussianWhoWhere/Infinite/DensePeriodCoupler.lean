import Mathlib
import GaussianWhoWhere.Infinite.DensePeriodInterface

/-!
# Dense-period coupler (Infinite L3, foothold composition)

Composes `DensePeriodInterface` into a single application theorem:

> if `f : ℝ → ℂ` is continuous, has two real periods `a, b`, and the
> integer span of `a, b` is dense in `ℝ`, then `f` is constant.

The arithmetic Kronecker-style density theorem (two incommensurable
real shifts generate a dense additive subgroup) is **not** proved
here; it remains the predicate
`TwoIncommensurablePeriodsGenerateDense` from
`DensePeriodInterface.lean`. This coupler simply consumes the density
hypothesis and combines it with `integer_span_periods` and
`dense_periods_force_const_on_real`.
-/

noncomputable section

namespace GaussianWhoWhere

/-- The integer span of two real shifts, expressed in the `*`-form
that `TwoIncommensurablePeriodsGenerateDense` uses. -/
def IntegerPeriodSpan (a b : ℝ) : Set ℝ :=
  {p : ℝ | ∃ m n : ℤ, p = (m : ℝ) * a + (n : ℝ) * b}

/-- Bridge: `IntegerPeriodSpan a b ⊆ PeriodSet f` whenever `a` and
`b` are periods of `f`. The two sets use different notations
(`(m : ℝ) * a` versus `m • a`); we convert via `zsmul_eq_mul`. -/
private theorem integer_period_span_subset_periodSet
    {f : ℝ → ℂ} {a b : ℝ}
    (ha : IsPeriod f a) (hb : IsPeriod f b) :
    IntegerPeriodSpan a b ⊆ PeriodSet f := by
  intro p hp
  rcases hp with ⟨m, n, hpdef⟩
  -- Translate `*`-form back to `•`-form before applying integer_span_periods.
  have hsmul : p = m • a + n • b := by
    rw [zsmul_eq_mul, zsmul_eq_mul, hpdef]
  rw [hsmul]
  exact integer_span_periods ha hb m n

/-- **Coupler theorem.** A continuous `f : ℝ → ℂ` with two periods
`a, b` whose integer span is dense in `ℝ` is constant. -/
theorem two_periods_dense_span_force_const
    {f : ℝ → ℂ} {a b : ℝ}
    (hf : Continuous f)
    (ha : IsPeriod f a) (hb : IsPeriod f b)
    (hdense : Dense (IntegerPeriodSpan a b)) :
    ∀ x y : ℝ, f x = f y := by
  apply dense_periods_force_const_on_real hf
  exact hdense.mono (integer_period_span_subset_periodSet ha hb)

/-- Specialized form for the existing arithmetic predicate
`TwoIncommensurablePeriodsGenerateDense`: if the predicate holds and
`f` is continuous with periods `a, b`, then `f` is constant. -/
theorem two_incommensurable_periods_force_const
    {f : ℝ → ℂ} {a b : ℝ}
    (hf : Continuous f)
    (ha : IsPeriod f a) (hb : IsPeriod f b)
    (hgen : TwoIncommensurablePeriodsGenerateDense a b) :
    ∀ x y : ℝ, f x = f y := by
  rcases hgen with ⟨_, _, _, hdense⟩
  -- The dense set in `TwoIncommensurablePeriodsGenerateDense` is
  -- definitionally `IntegerPeriodSpan a b`.
  exact two_periods_dense_span_force_const hf ha hb hdense

end GaussianWhoWhere
