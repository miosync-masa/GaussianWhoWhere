import Mathlib
import GaussianWhoWhere.Infinite.JensenCartwrightInterface
import GaussianWhoWhere.Infinite.WhereKillsExponentialFunctionLevelConcrete

/-!
# Jensen final pipeline (Infinite L3 headline)

Composes the last named analytic socket
`JensenCartwrightLinearZeroBound` directly into
`where_rigidity_concrete_full`. The result is the *paper-level*
headline theorem: under the standard concrete C3 hypotheses on `Q`
plus a single named analytic socket
`JensenCartwrightLinearZeroBound`, conclude `Q ≡ 1`.

In the language of the project status, "every analytic gap is
internalized in Lean except one named socket" is now a Lean
*theorem*, not a verbal claim.
-/

noncomputable section

namespace GaussianWhoWhere

/-- **Headline theorem of the Infinite Bridge C pipeline.**

Under the named Jensen / Cartwright socket
`JensenCartwrightLinearZeroBound` and the standard concrete C3 input
pack on `Q`, every linear-beating-sample-style
`TwoIncommensurableSampledWhoInputs` lifts to `Q ≡ 1`.

The single remaining analytic dependency is `hJC`; every other
hypothesis is a concrete predicate on `Q` (differentiability,
nonvanishing, normalization, analyticity of `complexLogDeriv Q`,
function-level Where) plus concrete data on the sampled who-inputs
(real-shift identifications, nonzero eigenvalues, and the irrational
shift ratio). -/
theorem where_rigidity_of_oddLogSample_from_jensenCartwright
    (hJC : JensenCartwrightLinearZeroBound)
    {Q : ℂ → ℂ}
    (hQ : FiniteExpType Q)
    (hQdiff : Differentiable ℂ Q)
    (hQnz : ∀ z : ℂ, Q z ≠ 0)
    (hQ0 : Q 0 = 1)
    (hLog : AnalyticOnNhd ℂ (complexLogDeriv Q) Set.univ)
    (hWhere : InfiniteWhere Q)
    (I :
      TwoIncommensurableSampledWhoInputs Q
        (fun u : ℕ → ℂ =>
          Nonempty (LinearZeroBoundBeatingLogSample u)))
    {a b : ℝ}
    (ha : I.inputs.input₁.a = (a : ℂ))
    (hb : I.inputs.input₂.a = (b : ℂ))
    (hA : I.inputs.input₁.A ≠ 0) (hB : I.inputs.input₂.A ≠ 0)
    (hirr : Irrational (a / b)) :
    Q = fun _ : ℂ => 1 :=
  where_rigidity_concrete_full
    (zeroDensityForcesZero_for_oddLogSample hJC)
    hQ hQdiff hQnz hQ0 hLog hWhere
    I ha hb hA hB hirr

end GaussianWhoWhere
