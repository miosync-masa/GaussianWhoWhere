import GaussianWhoWhere.Infinite.RealAxisConstToGlobalConcrete

/-!
# Reconstruction interface, normalized form (Infinite L3)

Refines the reconstruction interface by isolating the exact
differential-equation-solving input:

  `Q'/Q globally constant  +  Q 0 = 1
     ⇒ ExponentialSurvivor Q`.

This sharpens the previous abstract predicate
`GlobalLogDerivConstForcesExponentialSurvivor Q` (which lumped the
"solve and reconstruct exp" step together) into the narrower
`LogDerivEquationSolvesToExp Q`, gated by the normalization `Q 0 = 1`
that is anyway available from the surrounding pipeline (and which is
the standard form in which the differential-equation step is
typically stated).

The actual ODE-solving content is left as the predicate; once
internalized (e.g. via Mathlib's `is_const_of_deriv_eq_zero` applied
to `F(z) = Q z * exp(-c · z)`), the reconstruction gap closes
completely.
-/

noncomputable section

namespace GaussianWhoWhere

/-- **Normalized reconstruction interface.** A globally constant
log-derivative plus the normalization `Q 0 = 1` yields an exponential
survivor for `Q`. This is the narrower predicate the eventual ODE
solver will populate. -/
def LogDerivEquationSolvesToExp (Q : ℂ → ℂ) : Prop :=
  GloballyConstant (complexLogDeriv Q) →
    Q 0 = 1 →
      ExponentialSurvivor Q

/-- The previous abstract reconstruction predicate
`GlobalLogDerivConstForcesExponentialSurvivor Q` follows from the
normalized solver and the normalization `Q 0 = 1`. -/
theorem globalLogDerivConstForcesExponentialSurvivor_of_normalized_solver
    {Q : ℂ → ℂ}
    (hQ0 : Q 0 = 1)
    (hsolve : LogDerivEquationSolvesToExp Q) :
    GlobalLogDerivConstForcesExponentialSurvivor Q := by
  intro hconst
  exact hsolve hconst hQ0

/-- **Final pipeline → Q ≡ 1 with the reconstruction interface
specialized to the normalized solver.** Replaces
`GlobalLogDerivConstForcesExponentialSurvivor Q` by the pair
`Q 0 = 1` and `LogDerivEquationSolvesToExp Q`. -/
theorem where_rigidity_of_twoIncomm_sampled_differentiable_irrational_exponentLift_analyticLogDeriv_normalized
    {DenseEnough : (ℕ → ℂ) → Prop}
    (hZD : ZeroDensityForcesZero DenseEnough)
    {Q : ℂ → ℂ}
    (hQ : FiniteExpType Q)
    (hQdiff : Differentiable ℂ Q)
    (hQnz : ∀ z : ℂ, Q z ≠ 0)
    (hQ0 : Q 0 = 1)
    (hLog : AnalyticOnNhd ℂ (complexLogDeriv Q) Set.univ)
    (hsolve : LogDerivEquationSolvesToExp Q)
    (hlift : FunctionWhereForcesExponentReflection Q)
    (hWhere : InfiniteWhere Q)
    (I : TwoIncommensurableSampledWhoInputs Q DenseEnough)
    {a b : ℝ}
    (ha : I.inputs.input₁.a = (a : ℂ))
    (hb : I.inputs.input₂.a = (b : ℂ))
    (hA : I.inputs.input₁.A ≠ 0) (hB : I.inputs.input₂.A ≠ 0)
    (hirr : Irrational (a / b)) :
    Q = fun _ : ℂ => 1 :=
  where_rigidity_of_twoIncomm_sampled_differentiable_irrational_exponentLift_analyticLogDeriv
    hZD hQ hQdiff hQnz hLog
    (globalLogDerivConstForcesExponentialSurvivor_of_normalized_solver hQ0 hsolve)
    hlift hWhere I ha hb hA hB hirr

end GaussianWhoWhere
