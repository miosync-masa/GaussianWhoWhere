import Mathlib
import GaussianWhoWhere.Infinite.WhereKillsExponentialFunctionLevel

/-!
# Real-axis constant → globally constant: concrete witness from
analyticity (Infinite L3)

Internalizes the analytic-continuation interface
`RealAxisConstExtendsGlobally L` under the hypothesis that `L` is
analytic on a neighborhood of every point of `ℂ`. The proof is a
direct application of Mathlib's identity theorem
`AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure`: a real-axis
constant `c` accumulates at `0 : ℂ` from non-zero real points, so
`L` and the constant function `_ ↦ c` agree on the connected set
`Set.univ`.

This eliminates the abstract predicate
`LogDerivRealAxisConstExtendsGlobally Q` from the C3 pipeline as
soon as `complexLogDeriv Q` is supplied as analytic on `Set.univ`.
-/

noncomputable section

namespace GaussianWhoWhere

/-- **Identity-theorem witness.** A function analytic on a
neighborhood of every point of `ℂ` and constant on the real axis is
globally constant. -/
theorem realAxisConstExtendsGlobally_of_analyticOnNhd
    {L : ℂ → ℂ}
    (hL : AnalyticOnNhd ℂ L Set.univ) :
    RealAxisConstExtendsGlobally L := by
  rintro ⟨c, hreal⟩
  refine ⟨c, ?_⟩
  -- Constant function `C` and `L` agree on the (cluster) real axis at 0.
  let C : ℂ → ℂ := fun _ => c
  have hC : AnalyticOnNhd ℂ C Set.univ := analyticOnNhd_const
  have hclosure :
      (0 : ℂ) ∈ closure ({z : ℂ | L z = C z} \ ({0} : Set ℂ)) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    -- Pick the small real witness x = ε / 2 > 0.
    refine ⟨((ε / 2 : ℝ) : ℂ), ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · -- L ((ε/2 : ℝ) : ℂ) = c = C _.
        change L ((ε / 2 : ℝ) : ℂ) = c
        exact hreal (ε / 2)
      · -- ((ε/2 : ℝ) : ℂ) ≠ 0 since ε/2 > 0.
        have hxpos : (0 : ℝ) < ε / 2 := by positivity
        intro h
        have : ((ε / 2 : ℝ) : ℂ) = ((0 : ℝ) : ℂ) := by
          simpa using h
        have hxeq : (ε / 2 : ℝ) = 0 := by exact_mod_cast this
        exact (ne_of_gt hxpos) hxeq
    · -- dist (0 : ℂ) ((ε/2 : ℝ) : ℂ) < ε.
      have hxpos : (0 : ℝ) < ε / 2 := by positivity
      have hnorm : ‖((ε / 2 : ℝ) : ℂ)‖ = ε / 2 := by
        rw [Complex.norm_real]
        exact abs_of_pos hxpos
      rw [dist_eq_norm, zero_sub, norm_neg, hnorm]
      linarith
  -- Apply the identity theorem.
  have hEqOn : Set.EqOn L C Set.univ :=
    hL.eqOn_of_preconnected_of_mem_closure
      hC isPreconnected_univ (Set.mem_univ (0 : ℂ)) hclosure
  intro z
  exact hEqOn (Set.mem_univ z)

/-- **Concrete witness for `LogDerivRealAxisConstExtendsGlobally`.**
If `complexLogDeriv Q` is analytic on a neighborhood of every point
of `ℂ`, the real-axis-to-global extension predicate holds. -/
theorem logDerivRealAxisConstExtendsGlobally_of_analyticOnNhd
    {Q : ℂ → ℂ}
    (hLog : AnalyticOnNhd ℂ (complexLogDeriv Q) Set.univ) :
    LogDerivRealAxisConstExtendsGlobally Q :=
  realAxisConstExtendsGlobally_of_analyticOnNhd hLog

/-- **Final pipeline → Q ≡ 1 with the analytic-continuation interface
eliminated.** Replaces `LogDerivRealAxisConstExtendsGlobally Q` by
the concrete hypothesis `AnalyticOnNhd ℂ (complexLogDeriv Q) Set.univ`. -/
theorem where_rigidity_of_twoIncomm_sampled_differentiable_irrational_exponentLift_analyticLogDeriv
    {DenseEnough : (ℕ → ℂ) → Prop}
    (hZD : ZeroDensityForcesZero DenseEnough)
    {Q : ℂ → ℂ}
    (hQ : FiniteExpType Q)
    (hQdiff : Differentiable ℂ Q)
    (hQnz : ∀ z : ℂ, Q z ≠ 0)
    (hLog : AnalyticOnNhd ℂ (complexLogDeriv Q) Set.univ)
    (hrecon : GlobalLogDerivConstForcesExponentialSurvivor Q)
    (hlift : FunctionWhereForcesExponentReflection Q)
    (hWhere : InfiniteWhere Q)
    (I : TwoIncommensurableSampledWhoInputs Q DenseEnough)
    {a b : ℝ}
    (ha : I.inputs.input₁.a = (a : ℂ))
    (hb : I.inputs.input₂.a = (b : ℂ))
    (hA : I.inputs.input₁.A ≠ 0) (hB : I.inputs.input₂.A ≠ 0)
    (hirr : Irrational (a / b)) :
    Q = fun _ : ℂ => 1 :=
  where_rigidity_of_twoIncomm_sampled_differentiable_irrational_exponentLift
    hZD hQ hQdiff hQnz
    (logDerivRealAxisConstExtendsGlobally_of_analyticOnNhd hLog)
    hrecon hlift hWhere I ha hb hA hB hirr

end GaussianWhoWhere
