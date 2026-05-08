import Mathlib

/-!
# Concrete Hermite–Pochhammer polynomials (Level 3)

We record the concrete polynomials `P₄, P₈, P₁₂, P₁₆` and verify the
two structural facts the project relies on:

* reflection symmetry under `s ↦ 1 - s`;
* failure of additivity (witness for non-multiplicative behavior).
-/

noncomputable section

namespace GaussianWhoWhere

/-- Concrete polynomial `P₄(s) = 16s² − 16s + 12`. -/
def P4 (s : ℝ) : ℝ :=
  16 * s ^ 2 - 16 * s + 12

/-- Concrete polynomial `P₈(s) = 256s⁴ − 512s³ + 3200s² − 2944s + 1680`. -/
def P8 (s : ℝ) : ℝ :=
  256 * s ^ 4 - 512 * s ^ 3 + 3200 * s ^ 2 - 2944 * s + 1680

/-- Concrete polynomial `P₁₂`. -/
def P12 (s : ℝ) : ℝ :=
  4096 * s ^ 6
  - 12288 * s ^ 5
  + 209920 * s ^ 4
  - 399360 * s ^ 3
  + 1525504 * s ^ 2
  - 1327872 * s
  + 665280

/-- Concrete polynomial `P₁₆`. -/
def P16 (s : ℝ) : ℝ :=
  65536 * s ^ 8
  - 262144 * s ^ 7
  + 8716288 * s ^ 6
  - 25231360 * s ^ 5
  + 246636544 * s ^ 4
  - 451526656 * s ^ 3
  + 1345769472 * s ^ 2
  - 1124167680 * s
  + 518918400

theorem P4_symm (s : ℝ) : P4 s = P4 (1 - s) := by
  unfold P4
  ring

theorem P8_symm (s : ℝ) : P8 s = P8 (1 - s) := by
  unfold P8
  ring

theorem P12_symm (s : ℝ) : P12 s = P12 (1 - s) := by
  unfold P12
  ring

theorem P16_symm (s : ℝ) : P16 s = P16 (1 - s) := by
  unfold P16
  ring

theorem P4_not_additive : ∃ x y : ℝ, P4 (x + y) ≠ P4 x + P4 y := by
  refine ⟨1, 1, ?_⟩
  unfold P4
  norm_num

theorem P8_not_additive : ∃ x y : ℝ, P8 (x + y) ≠ P8 x + P8 y := by
  refine ⟨1, 1, ?_⟩
  unfold P8
  norm_num

theorem P12_not_additive : ∃ x y : ℝ, P12 (x + y) ≠ P12 x + P12 y := by
  refine ⟨1, 1, ?_⟩
  unfold P12
  norm_num

theorem P16_not_additive : ∃ x y : ℝ, P16 (x + y) ≠ P16 x + P16 y := by
  refine ⟨1, 1, ?_⟩
  unfold P16
  norm_num

/-! ## Polynomial-valued versions

The function-valued `P_k` defined above are convenient for `ring` and
`norm_num`, but the rigidity machinery in `PolynomialRigidity.lean`
operates on `Polynomial ℝ`. We mirror each `P_k` as a `Polynomial ℝ`
and record the `eval` identity. -/

open Polynomial in
/-- `P₄` as `Polynomial ℝ`. -/
def P4Poly : Polynomial ℝ :=
  16 * X ^ 2 - 16 * X + 12

open Polynomial in
/-- `P₈` as `Polynomial ℝ`. -/
def P8Poly : Polynomial ℝ :=
  256 * X ^ 4 - 512 * X ^ 3 + 3200 * X ^ 2 - 2944 * X + 1680

open Polynomial in
/-- `P₁₂` as `Polynomial ℝ`. -/
def P12Poly : Polynomial ℝ :=
  4096 * X ^ 6
  - 12288 * X ^ 5
  + 209920 * X ^ 4
  - 399360 * X ^ 3
  + 1525504 * X ^ 2
  - 1327872 * X
  + 665280

open Polynomial in
/-- `P₁₆` as `Polynomial ℝ`. -/
def P16Poly : Polynomial ℝ :=
  65536 * X ^ 8
  - 262144 * X ^ 7
  + 8716288 * X ^ 6
  - 25231360 * X ^ 5
  + 246636544 * X ^ 4
  - 451526656 * X ^ 3
  + 1345769472 * X ^ 2
  - 1124167680 * X
  + 518918400

@[simp] theorem eval_P4Poly (s : ℝ) : P4Poly.eval s = P4 s := by
  simp [P4Poly, P4]

@[simp] theorem eval_P8Poly (s : ℝ) : P8Poly.eval s = P8 s := by
  simp [P8Poly, P8]

@[simp] theorem eval_P12Poly (s : ℝ) : P12Poly.eval s = P12 s := by
  simp [P12Poly, P12]

@[simp] theorem eval_P16Poly (s : ℝ) : P16Poly.eval s = P16 s := by
  simp [P16Poly, P16]

end GaussianWhoWhere
