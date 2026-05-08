import Mathlib
import GaussianWhoWhere.Infinite.WhereKillsExponential

/-!
# Where kills exponential — concrete exponent-level core (Infinite L3, B2)

A concrete no-sorry theorem capturing the **algebraic core** of
"where kills the exponential survivor": once the reflection condition
has been lifted to the *exponent* level

  `∀ z, c · (1 − z) = c · z`,

the exponent constant `c` must be zero, hence `Q(z) = exp(c · z) ≡ 1`.

This is intentionally **not** a full proof of

  `exp(c · (1 − z)) = exp(c · z) ∀ z ⇒ c = 0`,

since that requires complex-exponential injectivity / periodicity
arguments not undertaken at this stage. The theorem here is the easy
algebraic foothold once the exponent equality is in hand; the analytic
lift from function-level `Q(1 − z) = Q(z)` to exponent-level
`c (1 − z) = c z` is the remaining gap and lives in a future round.

This file does **not** replace the existing `WhereKillsExponential`
interface; it provides a concrete companion theorem documenting the
unconditional algebraic step.
-/

noncomputable section

namespace GaussianWhoWhere

/-- Exponent-level reflection predicate: the linear exponent
`z ↦ c · z` is reflection-symmetric on the affine `z ↦ 1 − z`. -/
def ExponentReflection (c : ℂ) : Prop :=
  ∀ z : ℂ, c * (1 - z) = c * z

/-- The exponent-level reflection forces `c = 0`. -/
theorem exponentReflection_forces_zero
    {c : ℂ} (h : ExponentReflection c) :
    c = 0 := by
  have h0 := h 0
  -- c * (1 - 0) = c * 0  ⇒  c = 0
  simpa using h0

/-- Concrete exponential survivor: `Q` is exactly the linear
exponential `z ↦ exp(c · z)`. -/
def ConcreteExponentialSurvivor (Q : ℂ → ℂ) (c : ℂ) : Prop :=
  Q = fun z : ℂ => Complex.exp (c * z)

/-- **Concrete where-kills theorem (exponent level).** Once both the
linear-exponential form and the exponent-level reflection are known,
`Q` is the constant `1`. -/
theorem whereKillsExponentLevel
    {Q : ℂ → ℂ} {c : ℂ}
    (hExp : Q = fun z : ℂ => Complex.exp (c * z))
    (hWhereExp : ExponentReflection c) :
    Q = fun _ : ℂ => 1 := by
  have hc : c = 0 := exponentReflection_forces_zero hWhereExp
  subst hc
  funext z
  simp [hExp]

/-- Trivial bridge: a hypothesis stated as `∀ z, c (1 − z) = c z`
*is* `ExponentReflection c`. Useful as a name when consumers prefer
the explicit pointwise statement. -/
theorem exponentReflection_of_linearExponentWhere
    {c : ℂ} (h : ∀ z : ℂ, c * (1 - z) = c * z) :
    ExponentReflection c := h

end GaussianWhoWhere
