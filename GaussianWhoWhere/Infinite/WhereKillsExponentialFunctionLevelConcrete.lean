import Mathlib
import GaussianWhoWhere.Infinite.GlobalLogDerivConstToExpConcrete
import GaussianWhoWhere.Infinite.WhereKillsExponentialFunctionLevel

/-!
# Function-level Where lift, concrete witness (Infinite L3)

Internalizes the predicate `FunctionWhereForcesExponentReflection Q`
without any extra hypothesis on `Q`: function-level reflection
symmetry combined with the linear-exponential form `Q(z) = exp(c·z)`
forces the exponent reflection `c · (1 − z) = c · z`. The crux is

  `∀ z, exp(c(1−z)) = exp(cz)  ⇒  c = 0`,

proved by differentiating both sides at `z = 0` and using
`exp c = 1` (obtained from `z = 0`) to compare derivatives.

With this in hand the C3 pipeline accepts the function-level Where
hypothesis directly via `InfiniteWhere Q`, and the abstract
`FunctionWhereForcesExponentReflection Q` predicate is eliminated.
-/

noncomputable section

namespace GaussianWhoWhere

open Complex

/-- **Reflection of a linear exponent forces the exponent to vanish.**
If `exp(c(1 − z)) = exp(c · z)` for every `z : ℂ`, then `c = 0`.

Proof: take derivatives of the two functions at `z = 0`.

  d/dz exp(c (1 − z)) at z = 0  =  −c · exp c,
  d/dz exp(c · z)     at z = 0  =  c.

Plugging `z = 0` into the original equation gives `exp c = 1`, so
`−c · 1 = c`, i.e. `−c = c`, hence `c = 0`. -/
private theorem exp_linear_reflection_forces_zero
    {c : ℂ}
    (h : ∀ z : ℂ, Complex.exp (c * (1 - z)) = Complex.exp (c * z)) :
    c = 0 := by
  -- Step 1: function equality.
  have hfun :
      (fun z : ℂ => Complex.exp (c * (1 - z)))
        = fun z : ℂ => Complex.exp (c * z) := by
    funext z; exact h z
  -- Step 2: at z = 0, exp c = 1.
  have hexp_c : Complex.exp c = 1 := by
    have h0 := h 0
    simpa using h0
  -- Step 3: compute derivatives at z = 0.
  -- deriv (fun z => exp (c (1 − z))) 0.
  have hL_diff : DifferentiableAt ℂ (fun z : ℂ => c * (1 - z)) 0 := by
    exact (differentiableAt_const c).mul
      (differentiableAt_const 1 |>.sub differentiableAt_id)
  have hR_diff : DifferentiableAt ℂ (fun z : ℂ => c * z) 0 :=
    (differentiableAt_const c).mul differentiableAt_id
  have hLderiv :
      deriv (fun z : ℂ => Complex.exp (c * (1 - z))) 0
        = -c * Complex.exp c := by
    rw [deriv_cexp hL_diff]
    -- deriv (c * (1 - z)) at 0 = -c.
    have hd : deriv (fun z : ℂ => c * (1 - z)) 0 = -c := by
      rw [deriv_const_mul_field]
      -- deriv (1 - z) at 0 = -1.
      have : deriv (fun z : ℂ => (1 : ℂ) - z) 0 = -1 := by
        have h1 : deriv (fun z : ℂ => (1 : ℂ) - z) 0
            = deriv (fun _ : ℂ => (1 : ℂ)) 0 - deriv (fun z : ℂ => z) 0 := by
          exact deriv_sub (differentiableAt_const (1 : ℂ)) differentiableAt_id
        rw [h1, deriv_const, deriv_id'']
        ring
      rw [this]
      ring
    rw [hd]
    -- Goal: cexp (c * (1 - 0)) * (-c) = -c * cexp c.
    rw [show (1 : ℂ) - 0 = 1 from by ring, mul_one]
    ring
  have hRderiv :
      deriv (fun z : ℂ => Complex.exp (c * z)) 0 = c := by
    rw [deriv_cexp hR_diff]
    have hd : deriv (fun z : ℂ => c * z) 0 = c := by
      rw [deriv_const_mul_field]; simp
    -- Goal here is `cexp (c * 0) * deriv (fun z => c * z) 0 = c`.
    rw [hd, mul_zero, Complex.exp_zero, one_mul]
  -- Step 4: derivative equality from function equality.
  have hderivs :
      deriv (fun z : ℂ => Complex.exp (c * (1 - z))) 0
        = deriv (fun z : ℂ => Complex.exp (c * z)) 0 := by
    rw [hfun]
  rw [hLderiv, hRderiv] at hderivs
  -- hderivs : -c * exp c = c; rewrite exp c = 1 to get -c = c.
  rw [hexp_c, mul_one] at hderivs
  -- hderivs : -c = c. Manipulate to c = 0.
  -- Add c to both sides: -c + c = c + c, i.e. 0 = 2c.
  have hzero : (0 : ℂ) = c + c := by
    calc (0 : ℂ) = -c + c := by ring
      _ = c + c := by rw [hderivs]
  have h2c : (2 : ℂ) * c = 0 := by linear_combination -hzero
  have h2ne : (2 : ℂ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp h2c).resolve_left h2ne

/-- **Concrete witness for `FunctionWhereForcesExponentReflection`.** -/
theorem functionWhereForcesExponentReflection_concrete
    {Q : ℂ → ℂ} :
    FunctionWhereForcesExponentReflection Q := by
  intro hWhere c hExp
  -- exp(c (1−z)) = exp(c z) for every z.
  have hExpEq : ∀ z : ℂ, Complex.exp (c * (1 - z)) = Complex.exp (c * z) := by
    intro z
    have hw := hWhere.reflect z
    rw [hExp] at hw
    exact hw
  have hc : c = 0 := exp_linear_reflection_forces_zero hExpEq
  -- ExponentReflection 0 holds trivially.
  subst hc
  intro z
  ring

set_option linter.style.longLine false in
/-- Local short alias for the long-named upstream theorem so that the
final pipeline below stays inside the 100-character line limit. -/
private theorem _upstream_concreteReconstruction
    {DenseEnough : (ℕ → ℂ) → Prop}
    (hZD : ZeroDensityForcesZero DenseEnough)
    {Q : ℂ → ℂ}
    (hQ : FiniteExpType Q)
    (hQdiff : Differentiable ℂ Q)
    (hQnz : ∀ z : ℂ, Q z ≠ 0)
    (hQ0 : Q 0 = 1)
    (hLog : AnalyticOnNhd ℂ (complexLogDeriv Q) Set.univ)
    (hlift : FunctionWhereForcesExponentReflection Q)
    (hWhere : InfiniteWhere Q)
    (I : TwoIncommensurableSampledWhoInputs Q DenseEnough)
    {a b : ℝ}
    (ha : I.inputs.input₁.a = (a : ℂ))
    (hb : I.inputs.input₂.a = (b : ℂ))
    (hA : I.inputs.input₁.A ≠ 0) (hB : I.inputs.input₂.A ≠ 0)
    (hirr : Irrational (a / b)) :
    Q = fun _ : ℂ => 1 :=
  where_rigidity_of_twoIncomm_sampled_differentiable_irrational_exponentLift_analyticLogDeriv_concreteReconstruction
    hZD hQ hQdiff hQnz hQ0 hLog hlift hWhere I ha hb hA hB hirr

/-- **Final pipeline → Q ≡ 1 with the function-level Where lift
internalized.** Removes the predicate
`FunctionWhereForcesExponentReflection Q` from the input pack. -/
theorem where_rigidity_concrete_full
    {DenseEnough : (ℕ → ℂ) → Prop}
    (hZD : ZeroDensityForcesZero DenseEnough)
    {Q : ℂ → ℂ}
    (hQ : FiniteExpType Q)
    (hQdiff : Differentiable ℂ Q)
    (hQnz : ∀ z : ℂ, Q z ≠ 0)
    (hQ0 : Q 0 = 1)
    (hLog : AnalyticOnNhd ℂ (complexLogDeriv Q) Set.univ)
    (hWhere : InfiniteWhere Q)
    (I : TwoIncommensurableSampledWhoInputs Q DenseEnough)
    {a b : ℝ}
    (ha : I.inputs.input₁.a = (a : ℂ))
    (hb : I.inputs.input₂.a = (b : ℂ))
    (hA : I.inputs.input₁.A ≠ 0) (hB : I.inputs.input₂.A ≠ 0)
    (hirr : Irrational (a / b)) :
    Q = fun _ : ℂ => 1 :=
  _upstream_concreteReconstruction hZD hQ hQdiff hQnz hQ0 hLog
    functionWhereForcesExponentReflection_concrete
    hWhere I ha hb hA hB hirr

end GaussianWhoWhere
