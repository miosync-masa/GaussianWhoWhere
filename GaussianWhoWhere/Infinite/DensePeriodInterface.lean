import Mathlib

/-!
# Dense period interface (Infinite L3, foothold for the
exponential survivor argument)

Internalizes the easy *topological* consequence:

> a continuous function on `ℝ` whose period set is dense is constant.

The arithmetic theorem "two incommensurable shifts generate a dense
additive subgroup" is left as an interface predicate
(`TwoIncommensurablePeriodsGenerateDense`); proving it is delegated to
a future round.

We work in the concrete setting `ℝ → ℂ`, sufficient for the planned
use through `Q'/Q` along the real line. Generalization to abstract
topological additive groups is intentionally deferred.
-/

noncomputable section

namespace GaussianWhoWhere

/-! ## Period predicates -/

/-- `IsPeriod f p` means `p` is an additive period of `f`. -/
def IsPeriod {α β : Type*} [Add α] (f : α → β) (p : α) : Prop :=
  ∀ x : α, f (x + p) = f x

/-- The set of periods of `f : ℝ → ℂ`. -/
def PeriodSet (f : ℝ → ℂ) : Set ℝ :=
  {p : ℝ | IsPeriod f p}

/-- `f : ℝ → ℂ` has a dense period set. -/
def DensePeriodSet (f : ℝ → ℂ) : Prop :=
  Dense (PeriodSet f)

/-! ## Elementary algebraic properties of periods -/

theorem period_zero {α β : Type*} [AddZeroClass α] (f : α → β) :
    IsPeriod f 0 := by
  intro x
  rw [add_zero]

theorem period_neg {α β : Type*} [AddGroup α] {f : α → β} {p : α}
    (hp : IsPeriod f p) :
    IsPeriod f (-p) := by
  intro x
  -- Apply hp at (x + -p): f ((x + -p) + p) = f (x + -p).
  have h := hp (x + -p)
  -- (x + -p) + p = x.
  have h1 : (x + -p) + p = x := by
    rw [add_assoc, neg_add_cancel, add_zero]
  rw [h1] at h
  exact h.symm

theorem period_add {α β : Type*} [AddCommSemigroup α] {f : α → β}
    {p q : α} (hp : IsPeriod f p) (hq : IsPeriod f q) :
    IsPeriod f (p + q) := by
  intro x
  have hassoc : x + (p + q) = (x + p) + q := by
    rw [add_assoc]
  rw [hassoc, hq (x + p), hp x]

/-- Auxiliary: every nonneg-integer multiple of a period is a period. -/
private theorem nat_smul_period {α β : Type*} [AddCommGroup α]
    {f : α → β} {x : α} (hx : IsPeriod f x) :
    ∀ n : ℕ, IsPeriod f ((n : ℤ) • x) := by
  intro n
  induction n with
  | zero => simpa using period_zero (α := α) f
  | succ n ih =>
      have hcast : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
      have hstep : ((n + 1 : ℕ) : ℤ) • x = (n : ℤ) • x + x := by
        rw [hcast, add_smul, one_smul]
      rw [hstep]
      exact period_add ih hx

/-- Auxiliary: every integer multiple of a period is a period. -/
private theorem int_smul_period {α β : Type*} [AddCommGroup α]
    {f : α → β} {x : α} (hx : IsPeriod f x) :
    ∀ k : ℤ, IsPeriod f (k • x) := by
  intro k
  rcases k.eq_nat_or_neg with ⟨n, hn | hn⟩
  · subst hn
    exact nat_smul_period hx n
  · subst hn
    have hpos : IsPeriod f ((n : ℤ) • x) := nat_smul_period hx n
    have hneg : (-(n : ℤ)) • x = -((n : ℤ) • x) := by
      simp [neg_smul]
    rw [hneg]
    exact period_neg hpos

/-- Integer span of two periods is again a period (in a commutative
additive group). -/
theorem integer_span_periods {α β : Type*} [AddCommGroup α]
    {f : α → β} {a b : α}
    (ha : IsPeriod f a) (hb : IsPeriod f b) :
    ∀ m n : ℤ, IsPeriod f (m • a + n • b) := by
  intro m n
  exact period_add (int_smul_period ha m) (int_smul_period hb n)

/-! ## Topological foothold: dense periods force constancy -/

/-- **Main foothold.** A continuous `ℝ → ℂ` with a dense set of
periods is constant.

Proof: for every `x`, the maps `p ↦ f (x + p)` and `p ↦ f x` agree on
the dense `PeriodSet f`, hence everywhere by `Continuous.ext_on`. -/
theorem dense_periods_force_const_on_real
    {f : ℝ → ℂ}
    (hf : Continuous f)
    (hdense : Dense (PeriodSet f)) :
    ∀ x y : ℝ, f x = f y := by
  intro x y
  -- The "shifted-by-x" function and the constant value f x
  -- agree on PeriodSet f by definition; by density they agree everywhere.
  let g : ℝ → ℂ := fun p => f (x + p)
  let h : ℝ → ℂ := fun _ => f x
  have hg : Continuous g :=
    hf.comp (continuous_const.add continuous_id)
  have hh : Continuous h := continuous_const
  have heqOn : Set.EqOn g h (PeriodSet f) := by
    intro p hp
    -- hp : IsPeriod f p, so f (x + p) = f x
    exact hp x
  have hgh : g = h := hg.ext_on hdense hh heqOn
  -- Apply at p = y - x: g (y - x) = h (y - x), unfold both sides.
  have happ : f (x + (y - x)) = f x :=
    congrFun hgh (y - x)
  have hsimp : x + (y - x) = y := by ring
  rw [hsimp] at happ
  exact happ.symm

/-! ## Arithmetic interface (no proof) -/

/-- Predicate: two real shifts `a, b` are nonzero, incommensurable,
and their integer linear span is dense in `ℝ`. The density part is
the standard Kronecker-style theorem; we leave it as a predicate at
this layer and supply concrete instances later. -/
def TwoIncommensurablePeriodsGenerateDense (a b : ℝ) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ (∀ q : ℚ, a ≠ (q : ℝ) * b) ∧
    Dense ({p : ℝ | ∃ m n : ℤ, p = (m : ℝ) * a + (n : ℝ) * b} : Set ℝ)

end GaussianWhoWhere
