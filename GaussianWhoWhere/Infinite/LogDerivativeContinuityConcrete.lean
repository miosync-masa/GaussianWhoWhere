import Mathlib
import GaussianWhoWhere.Infinite.TwoIncommensurableSampledLogDerivConst

/-!
# Concrete witness for `LogDerivContinuousOnReal` (Infinite L3)

First concrete supply for the continuity interface

  `LogDerivContinuousOnReal Q
     := Continuous (RealRestrict (complexLogDeriv Q))`

from elementary continuity hypotheses on `Q` and `deriv Q` plus
nonvanishing of `Q`. With this in hand the sampled-input pipeline
no longer needs `LogDerivContinuousOnReal` as a primitive
hypothesis — callers may instead supply

* `Continuous Q`,
* `Continuous (fun z => deriv Q z)`,
* `∀ z, Q z ≠ 0`.

The continuity of `deriv Q` itself is the remaining future analytic
target; for entire / holomorphic `Q` this comes from holomorphicity
of the derivative, but no holomorphicity content is introduced at
this layer.
-/

noncomputable section

namespace GaussianWhoWhere

/-- **Concrete witness for `LogDerivContinuousOnReal`.** From
`Q` continuous, `deriv Q` continuous, and `Q` nonvanishing, we obtain
continuity of `complexLogDeriv Q` restricted to the real axis. -/
theorem logDerivContinuousOnReal_of_continuous_deriv
    {Q : ℂ → ℂ}
    (hderiv : Continuous (fun z : ℂ => deriv Q z))
    (hQcont : Continuous Q)
    (hQnz : ∀ z : ℂ, Q z ≠ 0) :
    LogDerivContinuousOnReal Q := by
  unfold LogDerivContinuousOnReal RealRestrict complexLogDeriv
  exact
    (hderiv.comp Complex.continuous_ofReal).div
      (hQcont.comp Complex.continuous_ofReal)
      (fun x => hQnz (x : ℂ))

/-- **Final sampled-input → log-derivative-constancy theorem with the
continuity interface eliminated.** Consumes only elementary
continuity hypotheses on `Q` and `deriv Q`, plus the standard
sampled / density / nonvanishing pack. -/
theorem complexLogDeriv_const_on_real_of_two_sampledWhoInputs_realShift_continuousDeriv
    {DenseEnough : (ℕ → ℂ) → Prop}
    (hZD : ZeroDensityForcesZero DenseEnough)
    {Q : ℂ → ℂ}
    (hQ : FiniteExpType Q)
    (hderiv : Continuous (fun z : ℂ => deriv Q z))
    (hQcont : Continuous Q)
    (hQnz : ∀ z : ℂ, Q z ≠ 0)
    (I : TwoSampledWhoInputs Q DenseEnough)
    {a b : ℝ}
    (ha : I.input₁.a = (a : ℂ))
    (hb : I.input₂.a = (b : ℂ))
    (hA : I.input₁.A ≠ 0) (hB : I.input₂.A ≠ 0)
    (hgen : TwoIncommensurablePeriodsGenerateDense a b) :
    ∀ x y : ℝ, complexLogDeriv Q (x : ℂ) = complexLogDeriv Q (y : ℂ) :=
  complexLogDeriv_const_on_real_of_two_sampledWhoInputs_realShift
    hZD hQ
    (logDerivContinuousOnReal_of_continuous_deriv hderiv hQcont hQnz)
    hQnz I ha hb hA hB hgen

/-- **Variant for `TwoIncommensurableSampledWhoInputs`.** Same
elementary-continuity input pack, consuming the bundled-density form. -/
theorem complexLogDeriv_const_on_real_of_twoIncomm_sampled_continuousDeriv
    {DenseEnough : (ℕ → ℂ) → Prop}
    (hZD : ZeroDensityForcesZero DenseEnough)
    {Q : ℂ → ℂ}
    (hQ : FiniteExpType Q)
    (hderiv : Continuous (fun z : ℂ => deriv Q z))
    (hQcont : Continuous Q)
    (hQnz : ∀ z : ℂ, Q z ≠ 0)
    (I : TwoIncommensurableSampledWhoInputs Q DenseEnough)
    {a b : ℝ}
    (ha : I.inputs.input₁.a = (a : ℂ))
    (hb : I.inputs.input₂.a = (b : ℂ))
    (hA : I.inputs.input₁.A ≠ 0) (hB : I.inputs.input₂.A ≠ 0)
    (hgen : TwoIncommensurablePeriodsGenerateDense a b) :
    ∀ x y : ℝ, complexLogDeriv Q (x : ℂ) = complexLogDeriv Q (y : ℂ) :=
  complexLogDeriv_const_on_real_of_twoIncommensurableSampledWhoInputs_realShift
    hZD hQ
    (logDerivContinuousOnReal_of_continuous_deriv hderiv hQcont hQnz)
    hQnz I ha hb hA hB hgen

end GaussianWhoWhere
