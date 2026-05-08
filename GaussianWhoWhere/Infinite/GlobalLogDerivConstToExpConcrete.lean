import Mathlib
import GaussianWhoWhere.Infinite.GlobalLogDerivConstToExpNormalized

/-!
# Reconstruction interface, concrete witness from `logDeriv_eqOn_iff`
(Infinite L3)

Internalizes the predicate

  `LogDerivEquationSolvesToExp Q
     := GloballyConstant (complexLogDeriv Q) → Q 0 = 1 → ExponentialSurvivor Q`

under the hypotheses

* `Differentiable ℂ Q`,
* `∀ z, Q z ≠ 0`.

The proof routes through Mathlib's

  `logDeriv_eqOn_iff
     : Set.EqOn (logDeriv f) (logDeriv g) s
         ↔ ∃ z ≠ 0, Set.EqOn f (z • g) s`

applied with `g = fun z => exp(c · z)`.

Since the project-local `complexLogDeriv` agrees with Mathlib's
`logDeriv` (`complexLogDeriv_eq_logDeriv`), the constancy hypothesis
on `complexLogDeriv Q` translates directly. The candidate
`g = exp(c · z)` has `logDeriv g = c` (constant), `g` nowhere
vanishes, and the differentiability is automatic. So
`Q = z₀ • exp(c · z)` for some nonzero `z₀`, and `Q 0 = 1` together
with `exp 0 = 1` forces `z₀ = 1`.

This eliminates the predicate `LogDerivEquationSolvesToExp Q` from
the C3 pipeline as soon as `Q` is differentiable and nonvanishing on
all of `ℂ`.
-/

noncomputable section

namespace GaussianWhoWhere

open Complex

/-- Mathlib's `logDeriv` of `z ↦ exp(c · z)` is the constant `c`. -/
private theorem logDeriv_cexp_const_mul (c : ℂ) :
    logDeriv (fun z : ℂ => Complex.exp (c * z)) = fun _ : ℂ => c := by
  funext z
  -- logDeriv f z = deriv f z / f z; numerator is c·exp(c·z), denominator is exp(c·z).
  have hlin : DifferentiableAt ℂ (fun w : ℂ => c * w) z :=
    (differentiableAt_const c).mul differentiableAt_id
  rw [logDeriv_apply, deriv_cexp hlin]
  -- deriv (fun w => c * w) z = c.
  have hderiv : deriv (fun w : ℂ => c * w) z = c := by
    rw [deriv_const_mul_field]
    simp
  rw [hderiv]
  field_simp [Complex.exp_ne_zero]

/-- **Concrete witness for `LogDerivEquationSolvesToExp`.** From
`Q` differentiable on `ℂ` and `Q` nowhere vanishing, the predicate
`LogDerivEquationSolvesToExp Q` follows from Mathlib's
`logDeriv_eqOn_iff`. -/
theorem logDerivEquationSolvesToExp_of_differentiable_nonvanishing
    {Q : ℂ → ℂ}
    (hQdiff : Differentiable ℂ Q)
    (hQnz : ∀ z : ℂ, Q z ≠ 0) :
    LogDerivEquationSolvesToExp Q := by
  intro hconst hQ0
  rcases hconst with ⟨c, hc⟩
  -- Candidate: E z = exp(c·z).
  set E : ℂ → ℂ := fun z : ℂ => Complex.exp (c * z) with hE
  have hEdiff : Differentiable ℂ E := by
    show Differentiable ℂ (fun z : ℂ => Complex.exp (c * z))
    exact ((differentiable_const c).mul differentiable_id).cexp
  have hEnz : ∀ z : ℂ, E z ≠ 0 := by
    intro z
    show Complex.exp (c * z) ≠ 0
    exact Complex.exp_ne_zero _
  have hLogE : logDeriv E = fun _ : ℂ => c := by
    show logDeriv (fun z : ℂ => Complex.exp (c * z)) = fun _ : ℂ => c
    exact logDeriv_cexp_const_mul c
  -- Bridge complexLogDeriv → logDeriv on Q.
  have hLogQ : ∀ z : ℂ, logDeriv Q z = c := by
    intro z
    rw [show logDeriv Q = complexLogDeriv Q from
        (complexLogDeriv_eq_logDeriv Q).symm]
    exact hc z
  -- Hypothesis of logDeriv_eqOn_iff: equality on Set.univ.
  have hEqLog : Set.EqOn (logDeriv Q) (logDeriv E) Set.univ := by
    intro z _
    rw [hLogQ z]
    show c = logDeriv E z
    rw [hLogE]
  -- Apply logDeriv_eqOn_iff.
  have hEqOn : ∃ z₀ : ℂ, z₀ ≠ 0 ∧ Set.EqOn Q (z₀ • E) Set.univ :=
    (logDeriv_eqOn_iff
      hQdiff.differentiableOn hEdiff.differentiableOn
      isOpen_univ isPreconnected_univ
      (fun z _ => hEnz z) (fun z _ => hQnz z)).mp hEqLog
  rcases hEqOn with ⟨z₀, _, hQE⟩
  -- Determine z₀ from Q 0 = 1.
  have hz₀ : z₀ = 1 := by
    have h0 : Q 0 = (z₀ • E) 0 := hQE (Set.mem_univ (0 : ℂ))
    rw [hQ0] at h0
    have : (1 : ℂ) = z₀ * Complex.exp (c * 0) := by
      simpa [E, smul_eq_mul] using h0
    simpa using this.symm
  -- Conclude Q = exp(c · ·).
  refine ⟨c, ?_⟩
  funext z
  have hz : Q z = (z₀ • E) z := hQE (Set.mem_univ z)
  rw [hz₀] at hz
  show Q z = Complex.exp (c * z)
  simpa [E, smul_eq_mul] using hz

/-- **Final pipeline → Q ≡ 1 with the reconstruction interface
eliminated.** The predicate `LogDerivEquationSolvesToExp Q` is now
supplied automatically by `Differentiable ℂ Q` and the nonvanishing
hypothesis `(∀ z, Q z ≠ 0)`. -/
theorem where_rigidity_of_twoIncomm_sampled_differentiable_irrational_exponentLift_analyticLogDeriv_concreteReconstruction
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
  where_rigidity_of_twoIncomm_sampled_differentiable_irrational_exponentLift_analyticLogDeriv_normalized
    hZD hQ hQdiff hQnz hQ0 hLog
    (logDerivEquationSolvesToExp_of_differentiable_nonvanishing hQdiff hQnz)
    hlift hWhere I ha hb hA hB hirr

end GaussianWhoWhere
