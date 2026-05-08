import Mathlib

/-!
# Functional-equation freezing (Bridge C, real-displacement core)

We formalize the algebraic core of:

> *Where symmetry freezes first-order real displacement.*

Concretely: if `D : ℂ` is purely imaginary (and nonzero), then for any
real parameters `eps, h`, the first-order response

  `−(eps · h) / D`

has zero real part. In the project's interpretive language, the
"Where axis" of a function under reflection symmetry $\Lambda(1-s) =
\Lambda(s)$ produces, at first order, displacements *along the
imaginary direction only*; the real part of the response is frozen.

This file is purely algebraic: it does not connect to any specific
analytic object (Hermite–Pochhammer or zeta) and does not claim RH.
It only fixes the algebraic identity behind the Bridge C
"Re-freezing operator" interpretation.
-/

noncomputable section

namespace GaussianWhoWhere

/-- A complex number with vanishing imaginary part. -/
def IsRealComplex (z : ℂ) : Prop := z.im = 0

/-- A complex number with vanishing real part. -/
def IsPureImagComplex (z : ℂ) : Prop := z.re = 0

/-! ## Closure lemmas for `IsRealComplex` / `IsPureImagComplex` -/

theorem realComplex_of_real (x : ℝ) :
    IsRealComplex (x : ℂ) := by
  unfold IsRealComplex
  simp

theorem pureImag_mul_I (y : ℝ) :
    IsPureImagComplex ((y : ℂ) * Complex.I) := by
  unfold IsPureImagComplex
  simp

theorem pureImag_neg (z : ℂ) (hz : IsPureImagComplex z) :
    IsPureImagComplex (-z) := by
  unfold IsPureImagComplex at hz ⊢
  simp [hz]

theorem real_mul_pureImag
    {a z : ℂ}
    (ha : IsRealComplex a) (hz : IsPureImagComplex z) :
    IsPureImagComplex (a * z) := by
  unfold IsRealComplex at ha
  unfold IsPureImagComplex at hz ⊢
  rw [Complex.mul_re, ha, hz]
  ring

/-! ## Parameterized first-order response -/

/-- **Parameterized form.** For real `eps, h, y` with `y ≠ 0`, the
quotient `−(eps · h) / (y · I)` is purely imaginary. -/
theorem firstOrderResponse_pureImag_param
    {eps h y : ℝ} (_hy : y ≠ 0) :
    IsPureImagComplex (-((eps : ℂ) * (h : ℂ)) / ((y : ℂ) * Complex.I)) := by
  unfold IsPureImagComplex
  rw [Complex.div_re]
  simp [Complex.normSq, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im]

/-! ## Generic first-order response

The main statement we want to expose downstream. The proof reduces
the case `D : ℂ` of `IsPureImagComplex D` and `D ≠ 0` to the
parameterized form by writing `D = (D.im : ℂ) · I` and noting
`D.im ≠ 0`. -/

theorem firstOrderResponse_pureImag_real
    {eps h : ℝ} {D : ℂ}
    (hD : IsPureImagComplex D) (hDnz : D ≠ 0) :
    IsPureImagComplex (-((eps : ℂ) * (h : ℂ)) / D) := by
  -- Set y := D.im. From hD : D.re = 0 and hDnz : D ≠ 0, deduce y ≠ 0.
  set y : ℝ := D.im with hy_def
  have hy_ne : y ≠ 0 := by
    intro hy0
    apply hDnz
    apply Complex.ext
    · exact hD
    · rw [Complex.zero_im]; exact hy0
  -- Rewrite D as (y : ℂ) · I.
  have hD_eq : D = (y : ℂ) * Complex.I := by
    apply Complex.ext
    · rw [hD]
      simp [Complex.mul_re, Complex.I_re, Complex.I_im]
    · rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]
      ring
  rw [hD_eq]
  exact firstOrderResponse_pureImag_param hy_ne

/-! ## Paper-facing theorems -/

/-- **Bridge C: Where freezes the real part of first-order response.**

Under the algebraic Where condition (`D` is purely imaginary, nonzero),
the first-order response `−(eps · h) / D` to real parameters has zero
real part. -/
theorem bridgeC_where_firstOrder_freezes_Re
    {eps h : ℝ} {D : ℂ}
    (hD : IsPureImagComplex D) (hDnz : D ≠ 0) :
    (-((eps : ℂ) * (h : ℂ)) / D).re = 0 :=
  firstOrderResponse_pureImag_real hD hDnz

/-- Application-flavored alias of the same theorem. -/
theorem where_firstOrder_response_has_zero_real_part
    {eps h : ℝ} {D : ℂ}
    (hD : IsPureImagComplex D) (hDnz : D ≠ 0) :
    (-((eps : ℂ) * (h : ℂ)) / D).re = 0 :=
  bridgeC_where_firstOrder_freezes_Re hD hDnz

end GaussianWhoWhere
