import GaussianWhoWhere.Infinite.DensePeriodCoupler

/-!
# Log-derivative coupler scaffolding (Infinite L3)

We do **not** introduce analytic derivative definitions or any
nonvanishing / `Q'/Q` content here. The single mechanical content is:

> If a function `L : ℂ → ℂ` is invariant under translation by a real
> shift `a` (i.e. `L(z + a) = L(z)` for all `z : ℂ`), then its
> restriction to the real line `t ↦ L(t : ℂ)` has `a` as an additive
> period. Consequently, two such real shifts together with a dense
> integer-span hypothesis force `L` to be constant on the real line.

This is the routing layer that the eventual `Q'/Q`-style argument
will use: once the analytic step shows that the log-derivative has
two incommensurable real periods, the conclusion drops out of the
already-proved `DensePeriodCoupler`.
-/

noncomputable section

namespace GaussianWhoWhere

/-- Real-line restriction of a complex function. -/
def RealRestrict (L : ℂ → ℂ) : ℝ → ℂ :=
  fun t => L (t : ℂ)

/-- `L : ℂ → ℂ` has the real shift `a : ℝ` as a period
(at the complex level). -/
def ComplexRealPeriod (L : ℂ → ℂ) (a : ℝ) : Prop :=
  ∀ z : ℂ, L (z + (a : ℂ)) = L z

/-- A complex-level real period descends to an additive period of the
real-line restriction. -/
theorem isPeriod_realRestrict_of_complexRealPeriod
    {L : ℂ → ℂ} {a : ℝ}
    (ha : ComplexRealPeriod L a) :
    IsPeriod (RealRestrict L) a := by
  intro t
  unfold RealRestrict
  -- Goal: L ((t + a : ℝ) : ℂ) = L (t : ℂ).
  -- Cast `(t + a : ℝ) : ℂ = (t : ℂ) + (a : ℂ)` and apply ha at (t : ℂ).
  have hcast : ((t + a : ℝ) : ℂ) = (t : ℂ) + (a : ℂ) := by
    push_cast; ring
  rw [hcast]
  exact ha (t : ℂ)

/-- **Coupler.** Two complex-level real periods with a dense
integer-span hypothesis force `L` to take a single value on the real
line, provided its real restriction is continuous. -/
theorem two_complex_real_periods_dense_force_const_on_real
    {L : ℂ → ℂ} {a b : ℝ}
    (hcont : Continuous (RealRestrict L))
    (ha : ComplexRealPeriod L a) (hb : ComplexRealPeriod L b)
    (hdense : Dense (IntegerPeriodSpan a b)) :
    ∀ x y : ℝ, L (x : ℂ) = L (y : ℂ) :=
  two_periods_dense_span_force_const hcont
    (isPeriod_realRestrict_of_complexRealPeriod ha)
    (isPeriod_realRestrict_of_complexRealPeriod hb)
    hdense

/-- Specialized form consuming the existing arithmetic predicate
`TwoIncommensurablePeriodsGenerateDense`. -/
theorem two_incommensurable_complex_real_periods_force_const_on_real
    {L : ℂ → ℂ} {a b : ℝ}
    (hcont : Continuous (RealRestrict L))
    (ha : ComplexRealPeriod L a) (hb : ComplexRealPeriod L b)
    (hgen : TwoIncommensurablePeriodsGenerateDense a b) :
    ∀ x y : ℝ, L (x : ℂ) = L (y : ℂ) :=
  two_incommensurable_periods_force_const hcont
    (isPeriod_realRestrict_of_complexRealPeriod ha)
    (isPeriod_realRestrict_of_complexRealPeriod hb)
    hgen

end GaussianWhoWhere
