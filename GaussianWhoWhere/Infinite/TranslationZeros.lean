import Mathlib
import GaussianWhoWhere.Infinite.TwoShiftCoupler

/-!
# Translation-eigen zero propagation (Infinite L3, B3)

Elementary algebraic consequences of a global translation
eigen-relation `Q(z + a) = A · Q(z)` for the zero set of `Q`:

* one-step forward propagation `Q(z) = 0 ⇒ Q(z + a) = 0`,
* `ℕ`-orbit forward propagation,
* one-step backward propagation when `A ≠ 0`,
* full `ℤ`-orbit propagation when `A ≠ 0`.

We then provide wrappers specialized to the existing
`TwoGlobalTranslationEigen` structure (one wrapper per `trans₁` /
`trans₂` field).

This file does not undertake the dense-orbit contradiction or the
exponential survivor argument; it is the elementary foothold that
later files will consume.
-/

noncomputable section

namespace GaussianWhoWhere

/-! ## Forward propagation -/

/-- One-step forward propagation along the eigen-direction. -/
theorem zero_propagates_one_step
    {Q : ℂ → ℂ} {a A z : ℂ}
    (h : ∀ w : ℂ, Q (w + a) = A * Q w)
    (hz : Q z = 0) :
    Q (z + a) = 0 := by
  rw [h z, hz, mul_zero]

/-- Full `ℕ`-orbit forward propagation. -/
theorem zero_propagates_nat
    {Q : ℂ → ℂ} {a A z : ℂ}
    (h : ∀ w : ℂ, Q (w + a) = A * Q w)
    (hz : Q z = 0) :
    ∀ n : ℕ, Q (z + (n : ℂ) * a) = 0 := by
  intro n
  induction n with
  | zero => simpa using hz
  | succ n ih =>
      have hgeom : z + ((n + 1 : ℕ) : ℂ) * a = (z + (n : ℂ) * a) + a := by
        push_cast; ring
      rw [hgeom, h, ih, mul_zero]

/-! ## Backward propagation (requires `A ≠ 0`) -/

/-- One-step backward propagation when the eigenvalue is nonzero. -/
theorem zero_propagates_backward_one_step
    {Q : ℂ → ℂ} {a A z : ℂ}
    (h : ∀ w : ℂ, Q (w + a) = A * Q w)
    (hA : A ≠ 0)
    (hz : Q z = 0) :
    Q (z - a) = 0 := by
  have hstep : Q ((z - a) + a) = A * Q (z - a) := h (z - a)
  have hcancel : (z - a) + a = z := by ring
  rw [hcancel] at hstep
  -- hstep : Q z = A * Q (z - a); use hz to deduce A * Q(z - a) = 0
  have hAQ : A * Q (z - a) = 0 := by rw [← hstep]; exact hz
  rcases mul_eq_zero.mp hAQ with hAzero | hQzero
  · exact absurd hAzero hA
  · exact hQzero

/-- Full `ℤ`-orbit propagation when the eigenvalue is nonzero. -/
theorem zero_propagates_int
    {Q : ℂ → ℂ} {a A z : ℂ}
    (h : ∀ w : ℂ, Q (w + a) = A * Q w)
    (hA : A ≠ 0)
    (hz : Q z = 0) :
    ∀ m : ℤ, Q (z + (m : ℂ) * a) = 0 := by
  intro m
  -- Strategy: prove the ℕ-step analog for backward orbits separately,
  -- then case-split on the sign of m.
  have forward : ∀ n : ℕ, Q (z + (n : ℂ) * a) = 0 :=
    zero_propagates_nat h hz
  have backward : ∀ n : ℕ, Q (z - (n : ℂ) * a) = 0 := by
    intro n
    induction n with
    | zero => simpa using hz
    | succ n ih =>
        -- target: Q (z - (n+1) * a) = 0
        -- rewrite: z - (n+1) * a = (z - n * a) - a
        have hgeom : z - ((n + 1 : ℕ) : ℂ) * a = (z - (n : ℂ) * a) - a := by
          push_cast; ring
        rw [hgeom]
        exact zero_propagates_backward_one_step h hA ih
  rcases m.eq_nat_or_neg with ⟨n, hn | hn⟩
  · -- m = n ≥ 0
    subst hn
    have := forward n
    simpa using this
  · -- m = -n
    subst hn
    have hb := backward n
    -- Q (z - n * a) = 0; rewrite as Q (z + ((-n : ℤ) : ℂ) * a) = 0
    have heq : (z + (((-(n : ℤ)) : ℤ) : ℂ) * a) = z - (n : ℂ) * a := by
      push_cast; ring
    rw [heq]
    exact hb

/-! ## Wrappers for `TwoGlobalTranslationEigen`

Each of the two translation eigen-relations packaged in
`TwoGlobalTranslationEigen` propagates zeros along its own orbit. -/

/-- One-step forward propagation along the `a₁`-direction of a
`TwoGlobalTranslationEigen`. -/
theorem TwoGlobalTranslationEigen.zero_propagates_one_step₁
    {Q : ℂ → ℂ} (G : TwoGlobalTranslationEigen Q) {z : ℂ}
    (hz : Q z = 0) :
    Q (z + G.a₁) = 0 :=
  GaussianWhoWhere.zero_propagates_one_step G.trans₁ hz

/-- One-step forward propagation along the `a₂`-direction of a
`TwoGlobalTranslationEigen`. -/
theorem TwoGlobalTranslationEigen.zero_propagates_one_step₂
    {Q : ℂ → ℂ} (G : TwoGlobalTranslationEigen Q) {z : ℂ}
    (hz : Q z = 0) :
    Q (z + G.a₂) = 0 :=
  GaussianWhoWhere.zero_propagates_one_step G.trans₂ hz

/-- `ℕ`-orbit forward propagation along the `a₁`-direction. -/
theorem TwoGlobalTranslationEigen.zero_propagates_nat₁
    {Q : ℂ → ℂ} (G : TwoGlobalTranslationEigen Q) {z : ℂ}
    (hz : Q z = 0) :
    ∀ n : ℕ, Q (z + (n : ℂ) * G.a₁) = 0 :=
  GaussianWhoWhere.zero_propagates_nat G.trans₁ hz

/-- `ℕ`-orbit forward propagation along the `a₂`-direction. -/
theorem TwoGlobalTranslationEigen.zero_propagates_nat₂
    {Q : ℂ → ℂ} (G : TwoGlobalTranslationEigen Q) {z : ℂ}
    (hz : Q z = 0) :
    ∀ n : ℕ, Q (z + (n : ℂ) * G.a₂) = 0 :=
  GaussianWhoWhere.zero_propagates_nat G.trans₂ hz

/-- `ℤ`-orbit propagation along the `a₁`-direction, assuming the
eigenvalue `A₁` is nonzero. -/
theorem TwoGlobalTranslationEigen.zero_propagates_int₁
    {Q : ℂ → ℂ} (G : TwoGlobalTranslationEigen Q)
    (hA : G.A₁ ≠ 0) {z : ℂ} (hz : Q z = 0) :
    ∀ m : ℤ, Q (z + (m : ℂ) * G.a₁) = 0 :=
  GaussianWhoWhere.zero_propagates_int G.trans₁ hA hz

/-- `ℤ`-orbit propagation along the `a₂`-direction, assuming the
eigenvalue `A₂` is nonzero. -/
theorem TwoGlobalTranslationEigen.zero_propagates_int₂
    {Q : ℂ → ℂ} (G : TwoGlobalTranslationEigen Q)
    (hA : G.A₂ ≠ 0) {z : ℂ} (hz : Q z = 0) :
    ∀ m : ℤ, Q (z + (m : ℂ) * G.a₂) = 0 :=
  GaussianWhoWhere.zero_propagates_int G.trans₂ hA hz

end GaussianWhoWhere
