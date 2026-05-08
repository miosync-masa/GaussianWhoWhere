import GaussianWhoWhere.Infinite.LogDerivativeContinuityHolomorphic

/-!
# Real-axis constant → globally constant interface (Infinite L3)

Packages the next analytic step:

> A function `L : ℂ → ℂ` constant on the real axis, together with an
> analytic-continuation bridge, is globally constant.

The analytic-continuation step (identity theorem on connected
holomorphic functions, applied to `L` and a constant function) is
**not** internalized here; it is recorded as the predicate
`RealAxisConstExtendsGlobally L` and supplied as an interface
hypothesis.

We also provide a `complexLogDeriv`-flavored alias and the end-to-end
sampled-input wrapper that delivers global constancy of
`complexLogDeriv Q` from the standard input pack plus this
extension interface.
-/

noncomputable section

namespace GaussianWhoWhere

/-- `L` is constant on the real axis. -/
def ConstantOnRealAxis (L : ℂ → ℂ) : Prop :=
  ∃ c : ℂ, ∀ x : ℝ, L (x : ℂ) = c

/-- `L` is globally constant on `ℂ`. -/
def GloballyConstant (L : ℂ → ℂ) : Prop :=
  ∃ c : ℂ, ∀ z : ℂ, L z = c

/-- **Analytic-continuation interface.** Real-axis constancy of `L`
extends to global constancy. The intended analytic content (identity
theorem on connected open sets) lives at the call site. -/
def RealAxisConstExtendsGlobally (L : ℂ → ℂ) : Prop :=
  ConstantOnRealAxis L → GloballyConstant L

/-- Pairwise real-axis equality is exactly real-axis constancy. -/
theorem constantOnRealAxis_of_pairwise_real_const
    {L : ℂ → ℂ}
    (h : ∀ x y : ℝ, L (x : ℂ) = L (y : ℂ)) :
    ConstantOnRealAxis L := by
  refine ⟨L (0 : ℂ), ?_⟩
  intro x
  -- L (x : ℂ) = L (0 : ℂ) by h applied at (x, 0); the cast (0 : ℝ) : ℂ
  -- equals (0 : ℂ) by simp.
  have hx0 : L (x : ℂ) = L ((0 : ℝ) : ℂ) := h x 0
  simpa using hx0

/-- Apply the extension interface. -/
theorem globallyConstant_of_realAxisConstExtends
    {L : ℂ → ℂ}
    (hext : RealAxisConstExtendsGlobally L)
    (hreal : ConstantOnRealAxis L) :
    GloballyConstant L :=
  hext hreal

/-- Pairwise real-axis equality plus the extension interface gives
global constancy. -/
theorem globallyConstant_of_pairwise_real_const
    {L : ℂ → ℂ}
    (hext : RealAxisConstExtendsGlobally L)
    (hreal : ∀ x y : ℝ, L (x : ℂ) = L (y : ℂ)) :
    GloballyConstant L :=
  hext (constantOnRealAxis_of_pairwise_real_const hreal)

/-! ## `complexLogDeriv`-flavored aliases -/

/-- The extension-interface predicate specialized to `complexLogDeriv Q`. -/
def LogDerivRealAxisConstExtendsGlobally (Q : ℂ → ℂ) : Prop :=
  RealAxisConstExtendsGlobally (complexLogDeriv Q)

/-- **Final sampled-input pipeline reaching global constancy of
`complexLogDeriv Q`.** Combines
`complexLogDeriv_const_on_real_of_twoIncomm_sampled_differentiable`
with the analytic-continuation interface
`LogDerivRealAxisConstExtendsGlobally Q`. -/
theorem globallyConstant_complexLogDeriv_of_twoIncomm_sampled_differentiable
    {DenseEnough : (ℕ → ℂ) → Prop}
    (hZD : ZeroDensityForcesZero DenseEnough)
    {Q : ℂ → ℂ}
    (hQ : FiniteExpType Q)
    (hQdiff : Differentiable ℂ Q)
    (hQnz : ∀ z : ℂ, Q z ≠ 0)
    (hext : LogDerivRealAxisConstExtendsGlobally Q)
    (I : TwoIncommensurableSampledWhoInputs Q DenseEnough)
    {a b : ℝ}
    (ha : I.inputs.input₁.a = (a : ℂ))
    (hb : I.inputs.input₂.a = (b : ℂ))
    (hA : I.inputs.input₁.A ≠ 0) (hB : I.inputs.input₂.A ≠ 0)
    (hgen : TwoIncommensurablePeriodsGenerateDense a b) :
    GloballyConstant (complexLogDeriv Q) := by
  apply globallyConstant_of_pairwise_real_const hext
  exact complexLogDeriv_const_on_real_of_twoIncomm_sampled_differentiable
    hZD hQ hQdiff hQnz I ha hb hA hB hgen

end GaussianWhoWhere
