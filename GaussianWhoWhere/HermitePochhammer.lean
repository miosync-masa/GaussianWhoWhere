import Mathlib
import GaussianWhoWhere.ConcretePolynomials

/-!
# Hermite–Pochhammer construction (Level 2 generators)

The concrete polynomials `P₄, P₈, P₁₂, P₁₆` defined in
`ConcretePolynomials.lean` are not arbitrary: they are produced by the
Hermite–Pochhammer expansion

  `P_{2n}(s) = Σ_{j=0}^{n} h_j · 2^j · (s/2)_j`

where `(s/2)_j = (s/2)(s/2+1)⋯(s/2 + j-1)` is the rising factorial
(Pochhammer symbol) and `h_j` are the physicists' Hermite-style
coefficients.

This file records the finite generators for `n = 2, 4, 6, 8` (i.e.
`P₄, P₈, P₁₂, P₁₆`) and proves that the resulting polynomials match
the concrete forms in `ConcretePolynomials.lean`.

We deliberately keep things finite: a general `P_{2n}` constructor is
not attempted here. The point is that each concrete `P_{2n}` for
`2n ∈ {4, 8, 12, 16}` is produced from a Hermite–Pochhammer pattern,
not from ad-hoc coefficients.
-/

noncomputable section

namespace GaussianWhoWhere

/-- Rising factorial `(a)_n = a · (a+1) · ⋯ · (a + n - 1)` over `ℝ`.

Placeholder: later this will support the general definition of
`P_{2n}` from the Hermite–Pochhammer expansion. -/
def risingFactorial (a : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => risingFactorial a n * (a + n)

@[simp] theorem risingFactorial_zero (a : ℝ) : risingFactorial a 0 = 1 := rfl

@[simp] theorem risingFactorial_succ (a : ℝ) (n : ℕ) :
    risingFactorial a (n + 1) = risingFactorial a n * (a + n) := rfl

/-- Hermite–Pochhammer expansion with finitely supported coefficients.

`hermitePochhammerOfCoeffs h n s = Σ_{j=0}^{n-1} h(j) · 2^j · (s/2)_j`. -/
def hermitePochhammerOfCoeffs (h : ℕ → ℝ) (n : ℕ) (s : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, h j * 2 ^ j * risingFactorial (s / 2) j

/-! ## Coefficient sequences for `P₄, P₈, P₁₂, P₁₆`

Each `H{2n}Coeff` is the finitely-supported function `j ↦ h_j` for the
expansion of `P_{2n}`. -/

/-- Hermite coefficients generating `P₄`: `(h_0, h_1, h_2) = (12, -48, 16)`. -/
def H4Coeff : ℕ → ℝ
  | 0 => 12
  | 1 => -48
  | 2 => 16
  | _ => 0

/-- Hermite coefficients generating `P₈`. -/
def H8Coeff : ℕ → ℝ
  | 0 => 1680
  | 1 => -13440
  | 2 => 13440
  | 3 => -3584
  | 4 => 256
  | _ => 0

/-- Hermite coefficients generating `P₁₂`. -/
def H12Coeff : ℕ → ℝ
  | 0 => 665280
  | 1 => -7983360
  | 2 => 13305600
  | 3 => -7096320
  | 4 => 1520640
  | 5 => -135168
  | 6 => 4096
  | _ => 0

/-- Hermite coefficients generating `P₁₆`. -/
def H16Coeff : ℕ → ℝ
  | 0 => 518918400
  | 1 => -8302694400
  | 2 => 19372953600
  | 3 => -15498362880
  | 4 => 5535129600
  | 5 => -984023040
  | 6 => 89456640
  | 7 => -3932160
  | 8 => 65536
  | _ => 0

/-- Generated `P₄` from `H4Coeff`. -/
def P4Gen (s : ℝ) : ℝ := hermitePochhammerOfCoeffs H4Coeff 3 s

/-- Generated `P₈` from `H8Coeff`. -/
def P8Gen (s : ℝ) : ℝ := hermitePochhammerOfCoeffs H8Coeff 5 s

/-- Generated `P₁₂` from `H12Coeff`. -/
def P12Gen (s : ℝ) : ℝ := hermitePochhammerOfCoeffs H12Coeff 7 s

/-- Generated `P₁₆` from `H16Coeff`. -/
def P16Gen (s : ℝ) : ℝ := hermitePochhammerOfCoeffs H16Coeff 9 s

/-! ## Generation theorems: each concrete `P_k` matches its Hermite–Pochhammer form. -/

theorem hermitePochhammer_H4_eq_P4 (s : ℝ) : P4Gen s = P4 s := by
  unfold P4Gen hermitePochhammerOfCoeffs P4
  simp [Finset.sum_range_succ, H4Coeff, risingFactorial]
  ring

theorem hermitePochhammer_H8_eq_P8 (s : ℝ) : P8Gen s = P8 s := by
  unfold P8Gen hermitePochhammerOfCoeffs P8
  simp [Finset.sum_range_succ, H8Coeff, risingFactorial]
  ring

theorem hermitePochhammer_H12_eq_P12 (s : ℝ) : P12Gen s = P12 s := by
  unfold P12Gen hermitePochhammerOfCoeffs P12
  simp [Finset.sum_range_succ, H12Coeff, risingFactorial]
  ring

theorem hermitePochhammer_H16_eq_P16 (s : ℝ) : P16Gen s = P16 s := by
  unfold P16Gen hermitePochhammerOfCoeffs P16
  simp [Finset.sum_range_succ, H16Coeff, risingFactorial]
  ring

end GaussianWhoWhere

/-! ## General `P_{2n}` construction (B-layer)

We promote the finite-coefficient construction to a polynomial-valued
form using `Polynomial.ascPochhammer`, and define a uniform
`P_{2n}` polynomial.

The Hermite-style coefficient `hermiteEvenCoeff n j` is the closed-form
coefficient of `y^{2j}` in the *physicists'* Hermite polynomial
`H_{2n}(y)`:

  `h(n, j) = (-1)^{n - j} · (2n)! / ((n - j)! · (2j)!) · 2^{2j}`,   `j ≤ n`,

zero otherwise. -/

namespace GaussianWhoWhere

open Polynomial

/-- The polynomial `(1/2) · X` in `Polynomial ℝ`. -/
def halfX : Polynomial ℝ := Polynomial.C ((1 : ℝ) / 2) * Polynomial.X

/-- Polynomial-valued Pochhammer at `s/2`:
`pochhammerHalfX j` evaluates to the rising factorial `(s/2)_j`. -/
def pochhammerHalfX (j : ℕ) : Polynomial ℝ :=
  (ascPochhammer ℝ j).comp halfX

@[simp] theorem eval_halfX (s : ℝ) : halfX.eval s = s / 2 := by
  unfold halfX
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  ring

theorem ascPochhammer_eval_eq_risingFactorial (a : ℝ) (n : ℕ) :
    (ascPochhammer ℝ n).eval a = risingFactorial a n := by
  induction n with
  | zero => simp [ascPochhammer_zero, risingFactorial]
  | succ n ih =>
      rw [ascPochhammer_succ_eval, ih]
      rfl

@[simp] theorem eval_pochhammerHalfX (j : ℕ) (s : ℝ) :
    (pochhammerHalfX j).eval s = risingFactorial (s / 2) j := by
  rw [pochhammerHalfX, eval_comp, eval_halfX,
      ascPochhammer_eval_eq_risingFactorial]

/-- The Hermite-style coefficient `h(n, j)` for the even-degree
expansion `H_{2n}(y) = Σ_{j ≤ n} h(n, j) · y^{2j}`. -/
def hermiteEvenCoeff (n j : ℕ) : ℝ :=
  if j ≤ n then
    (-1 : ℝ) ^ (n - j)
      * ((Nat.factorial (2 * n) : ℝ)
          / ((Nat.factorial (n - j) : ℝ) * (Nat.factorial (2 * j) : ℝ)))
      * (2 : ℝ) ^ (2 * j)
  else
    0

/-- General polynomial `P_{2n}(s) = Σ_{j ≤ n} h(n, j) · 2^j · (s/2)_j`
as `Polynomial ℝ`. -/
def P2nPoly (n : ℕ) : Polynomial ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    Polynomial.C (hermiteEvenCoeff n j * (2 : ℝ) ^ j) * pochhammerHalfX j

/-- Check that `hermiteEvenCoeff 2 j` reproduces the explicit
`H4Coeff j` for `j ≤ 2`. -/
theorem hermiteEvenCoeff_two_eq_H4Coeff (j : ℕ) (hj : j ≤ 2) :
    hermiteEvenCoeff 2 j = H4Coeff j := by
  interval_cases j <;>
    simp [hermiteEvenCoeff, H4Coeff, Nat.factorial]
  all_goals norm_num

theorem hermiteEvenCoeff_four_eq_H8Coeff (j : ℕ) (hj : j ≤ 4) :
    hermiteEvenCoeff 4 j = H8Coeff j := by
  interval_cases j <;>
    simp [hermiteEvenCoeff, H8Coeff, Nat.factorial]
  all_goals norm_num

theorem hermiteEvenCoeff_six_eq_H12Coeff (j : ℕ) (hj : j ≤ 6) :
    hermiteEvenCoeff 6 j = H12Coeff j := by
  interval_cases j <;>
    simp [hermiteEvenCoeff, H12Coeff, Nat.factorial]
  all_goals norm_num

theorem hermiteEvenCoeff_eight_eq_H16Coeff (j : ℕ) (hj : j ≤ 8) :
    hermiteEvenCoeff 8 j = H16Coeff j := by
  interval_cases j <;>
    simp [hermiteEvenCoeff, H16Coeff, Nat.factorial]
  all_goals norm_num

/-! ### Match between general `P2nPoly` and the explicit `P_kPoly`

For `n ∈ {2, 4, 6, 8}` the general construction `P2nPoly n` evaluates
to the concrete `P_k`. We give the eval-level identity; multiplying it
by `Polynomial.funext` would lift it to a polynomial equality, but the
eval form is what is consumed downstream. -/

theorem P2nPoly_two_eval_eq_P4 (s : ℝ) :
    (P2nPoly 2).eval s = P4 s := by
  simp only [P2nPoly, Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hermiteEvenCoeff_two_eq_H4Coeff 0 (by decide),
      hermiteEvenCoeff_two_eq_H4Coeff 1 (by decide),
      hermiteEvenCoeff_two_eq_H4Coeff 2 (by decide)]
  simp [H4Coeff, risingFactorial, P4]
  ring

theorem P2nPoly_four_eval_eq_P8 (s : ℝ) :
    (P2nPoly 4).eval s = P8 s := by
  simp only [P2nPoly, Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hermiteEvenCoeff_four_eq_H8Coeff 0 (by decide),
      hermiteEvenCoeff_four_eq_H8Coeff 1 (by decide),
      hermiteEvenCoeff_four_eq_H8Coeff 2 (by decide),
      hermiteEvenCoeff_four_eq_H8Coeff 3 (by decide),
      hermiteEvenCoeff_four_eq_H8Coeff 4 (by decide)]
  simp [H8Coeff, risingFactorial, P8]
  ring

theorem P2nPoly_six_eval_eq_P12 (s : ℝ) :
    (P2nPoly 6).eval s = P12 s := by
  simp only [P2nPoly, Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hermiteEvenCoeff_six_eq_H12Coeff 0 (by decide),
      hermiteEvenCoeff_six_eq_H12Coeff 1 (by decide),
      hermiteEvenCoeff_six_eq_H12Coeff 2 (by decide),
      hermiteEvenCoeff_six_eq_H12Coeff 3 (by decide),
      hermiteEvenCoeff_six_eq_H12Coeff 4 (by decide),
      hermiteEvenCoeff_six_eq_H12Coeff 5 (by decide),
      hermiteEvenCoeff_six_eq_H12Coeff 6 (by decide)]
  simp [H12Coeff, risingFactorial, P12]
  ring

theorem P2nPoly_eight_eval_eq_P16 (s : ℝ) :
    (P2nPoly 8).eval s = P16 s := by
  simp only [P2nPoly, Finset.sum_range_succ, Finset.sum_range_zero]
  rw [hermiteEvenCoeff_eight_eq_H16Coeff 0 (by decide),
      hermiteEvenCoeff_eight_eq_H16Coeff 1 (by decide),
      hermiteEvenCoeff_eight_eq_H16Coeff 2 (by decide),
      hermiteEvenCoeff_eight_eq_H16Coeff 3 (by decide),
      hermiteEvenCoeff_eight_eq_H16Coeff 4 (by decide),
      hermiteEvenCoeff_eight_eq_H16Coeff 5 (by decide),
      hermiteEvenCoeff_eight_eq_H16Coeff 6 (by decide),
      hermiteEvenCoeff_eight_eq_H16Coeff 7 (by decide),
      hermiteEvenCoeff_eight_eq_H16Coeff 8 (by decide)]
  simp [H16Coeff, risingFactorial, P16]
  ring

/-! ### Finite reflection symmetry harvest

For `n ∈ {2, 4, 6, 8}`, the eval equality `P2nPoly n .eval s = P_k s`
combined with the concrete `P_k_symm` lemma gives reflection symmetry
of the general construction at these specific `n`. -/

theorem P2nPoly_two_symm (s : ℝ) :
    (P2nPoly 2).eval (1 - s) = (P2nPoly 2).eval s := by
  rw [P2nPoly_two_eval_eq_P4, P2nPoly_two_eval_eq_P4]
  exact (P4_symm s).symm

theorem P2nPoly_four_symm (s : ℝ) :
    (P2nPoly 4).eval (1 - s) = (P2nPoly 4).eval s := by
  rw [P2nPoly_four_eval_eq_P8, P2nPoly_four_eval_eq_P8]
  exact (P8_symm s).symm

theorem P2nPoly_six_symm (s : ℝ) :
    (P2nPoly 6).eval (1 - s) = (P2nPoly 6).eval s := by
  rw [P2nPoly_six_eval_eq_P12, P2nPoly_six_eval_eq_P12]
  exact (P12_symm s).symm

theorem P2nPoly_eight_symm (s : ℝ) :
    (P2nPoly 8).eval (1 - s) = (P2nPoly 8).eval s := by
  rw [P2nPoly_eight_eval_eq_P16, P2nPoly_eight_eval_eq_P16]
  exact (P16_symm s).symm

/-- Conjectural reflection symmetry of the general `P_{2n}`.

For `n ∈ {2, 4, 6, 8}` (i.e. `2n ∈ {4, 8, 12, 16}`), `(-1)^n = 1` and
this reduces to `(P2nPoly n).eval (1 - s) = (P2nPoly n).eval s`,
matching the concrete `P_k_symm` lemmas (and proved at those `n` by
the four `P2nPoly_*_symm` theorems above). The general proof requires
a combinatorial identity on the Hermite even coefficients. We keep it
as a `Prop` rather than asserting an unproved theorem, so the formal
development contains no unfinished proof here. -/
def P2nPolyReflectConjecture : Prop :=
  ∀ (n : ℕ) (s : ℝ),
    (P2nPoly n).eval (1 - s) = (-1 : ℝ) ^ n * (P2nPoly n).eval s

/-! ## Scaled Pochhammer basis and three-term recurrence

We now upgrade the conjecture to a theorem. The strategy:

1. Re-express `P2nPoly` in the *scaled* Pochhammer basis
   `s_j(s) := 2^j · (s/2)_j`.
2. Derive the multiplication formula
   `(4s − 2) · s_j(s) = 4 · s_{j+1}(s) − (8j + 2) · s_j(s)` at the
   eval level.
3. Establish the Hermite-style three-term recurrence on coefficients
   (so far only its eval-level shadow on `P2nPoly` is needed).
4. Conclude `P_{n+1}(s) = (4s−2) P_n(s) + 8n(2n−1) P_{n−1}(s)`
   (eval form), and prove `P2nPoly_reflect` by two-step induction. -/

/-- Scaled Pochhammer basis: `2^j · (s/2)_j`, packaged as a real
polynomial. -/
def scaledPochhammerHalfX (j : ℕ) : Polynomial ℝ :=
  Polynomial.C ((2 : ℝ) ^ j) * pochhammerHalfX j

@[simp] theorem eval_scaledPochhammerHalfX (j : ℕ) (s : ℝ) :
    (scaledPochhammerHalfX j).eval s
      = (2 : ℝ) ^ j * risingFactorial (s / 2) j := by
  unfold scaledPochhammerHalfX
  simp

/-- Rewrite `P2nPoly` in the scaled basis. -/
lemma P2nPoly_eq_sum_scaled (n : ℕ) :
    P2nPoly n =
      ∑ j ∈ Finset.range (n + 1),
        Polynomial.C (hermiteEvenCoeff n j) * scaledPochhammerHalfX j := by
  unfold P2nPoly scaledPochhammerHalfX
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.C_mul]
  ring

/-- Eval of the scaled basis: `s_j(s) = 2^j (s/2)_j`. We avoid working
with `risingFactorial (s/2)` directly and instead expose the
**recurrence relation** between consecutive scaled basis values. -/
lemma scaledPochhammer_eval_succ (j : ℕ) (s : ℝ) :
    (scaledPochhammerHalfX (j + 1)).eval s
      = (s + 2 * (j : ℝ)) * (scaledPochhammerHalfX j).eval s := by
  simp [risingFactorial, pow_succ]
  ring

/-- The multiplication formula `(4s − 2) · s_j(s) =
4 · s_{j+1}(s) − (8j + 2) · s_j(s)` at the eval level. -/
lemma four_s_sub_two_mul_scaledPochhammer_eval (j : ℕ) (s : ℝ) :
    (4 * s - 2) * (scaledPochhammerHalfX j).eval s
      = 4 * (scaledPochhammerHalfX (j + 1)).eval s
          - (8 * (j : ℝ) + 2) * (scaledPochhammerHalfX j).eval s := by
  rw [scaledPochhammer_eval_succ]
  ring

/-! ## Hermite even-coefficient three-term recurrence

The closed-form coefficient `hermiteEvenCoeff n j` satisfies

  `h(n+1, k) = 4 · h(n, k − 1) − (8k + 2) · h(n, k)
                + 8n(2n − 1) · h(n − 1, k)`     for `k ≥ 1`,
  `h(n+1, 0) = -(8·0 + 2) · h(n, 0) + 8n(2n − 1) · h(n − 1, 0)`,

which is exactly the trace at the level of even-degree coefficients of
the physicists' Hermite recurrence

  `H_{2(n+1)}(y) = (something polynomial in y²) · H_{2n}(y) + ...`,

re-parameterized in `s = (1 + y²)/4`.

We avoid a frontal closed-form proof of this identity over all `n, k`.
Instead we use the *eval* version of the polynomial three-term
recurrence directly. -/

/-- Ratio between adjacent Hermite even coefficients in the `k` direction.

This is the factorial calculation behind the `4 · h(n,k-1)` contribution
in the three-term recurrence. It is stated after multiplying by
`n-k+1`, avoiding division in the lemma statement. -/
private lemma hermiteEvenCoeff_prev_ratio
    (n k : ℕ) (hkpos : 1 ≤ k) (hkle : k ≤ n) :
    (((n - k + 1 : ℕ) : ℝ)) * (4 * hermiteEvenCoeff n (k - 1))
      = - ((((2 * k : ℕ) : ℝ) * (((2 * k - 1 : ℕ) : ℝ)))
          * hermiteEvenCoeff n k) := by
  have hkm1 : k - 1 ≤ n := by omega
  have hnk1 : n - (k - 1) = n - k + 1 := by omega
  have h2k : 2 * k = 2 * (k - 1) + 2 := by omega
  have hfac2k :
      Nat.factorial (2 * k)
        = (2 * k) * (2 * k - 1) * Nat.factorial (2 * (k - 1)) := by
    rw [h2k]
    simp [Nat.factorial_succ]
    ring
  have hfacnk :
      Nat.factorial (n - k + 1) = (n - k + 1) * Nat.factorial (n - k) := by
    rw [show n - k + 1 = (n - k) + 1 by omega]
    simp [Nat.factorial_succ]
  have hpow : (2 : ℝ) ^ (2 * k) = 4 * (2 : ℝ) ^ (2 * (k - 1)) := by
    have hk2 : 2 * k = 2 * (k - 1) + 2 := by omega
    rw [hk2, pow_add]
    norm_num
    ring
  have hden_ne : (↑n - ↑k + 1 : ℝ) ≠ 0 := by
    have hkleR : (k : ℝ) ≤ n := by exact_mod_cast hkle
    nlinarith
  have hk_ne : (k : ℝ) ≠ 0 := by positivity
  have h2k1_ne : (((2 * k - 1 : ℕ) : ℝ)) ≠ 0 := by
    have hpos : 0 < 2 * k - 1 := by omega
    positivity
  simp [hermiteEvenCoeff, hkm1, hkle, hnk1, hfac2k, hfacnk, hpow]
  field_simp [hk_ne, h2k1_ne, hden_ne, Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)]
  ring_nf

set_option linter.flexible false in
/-- Ratio between `h(n+1,k)` and `h(n,k)`, again with the natural
denominator multiplied away. This handles the part of the recurrence
coming from the jump in the Hermite index. -/
private lemma hermiteEvenCoeff_next_ratio
    (n k : ℕ) (hkle : k ≤ n) :
    (((n + 1 - k : ℕ) : ℝ)) * hermiteEvenCoeff (n + 1) k
      = - ((((2 * n + 2 : ℕ) : ℝ) * (((2 * n + 1 : ℕ) : ℝ)))
          * hermiteEvenCoeff n k) := by
  have hklen1 : k ≤ n + 1 := by omega
  have hsub : n + 1 - k = n - k + 1 := by omega
  have hfac_num :
      Nat.factorial (2 * (n + 1))
        = (2 * n + 2) * (2 * n + 1) * Nat.factorial (2 * n) := by
    have h : 2 * (n + 1) = 2 * n + 2 := by omega
    rw [h]
    simp [Nat.factorial_succ]
    ring
  have hfacden :
      Nat.factorial (n - k + 1) = (n - k + 1) * Nat.factorial (n - k) := by
    rw [show n - k + 1 = (n - k) + 1 by omega]
    simp [Nat.factorial_succ]
  have hden_ne : (↑n + 1 - ↑k : ℝ) ≠ 0 := by
    have hkleR : (k : ℝ) ≤ n := by exact_mod_cast hkle
    nlinarith
  simp [hermiteEvenCoeff, hkle, hklen1, hsub, hfac_num]
  rw [hfacden]
  field_simp [hden_ne, Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)]
  norm_num [Nat.cast_add, Nat.cast_mul]
  rw [Nat.cast_sub hkle]
  ring_nf

set_option linter.flexible false in
/-- Ratio between `h(n,k)` and `h(n-1,k)`, with the two Hermite-index
step factors multiplied on the `h(n-1,k)` side. -/
private lemma hermiteEvenCoeff_prev_n_ratio
    (n k : ℕ) (hn : 1 ≤ n) (hkle : k ≤ n - 1) :
    (((n - k : ℕ) : ℝ)) * hermiteEvenCoeff n k
      = - ((((2 * n : ℕ) : ℝ) * (((2 * n - 1 : ℕ) : ℝ)))
          * hermiteEvenCoeff (n - 1) k) := by
  have hkle_n : k ≤ n := by omega
  have hsub : n - k = (n - 1) - k + 1 := by omega
  have hfac_num :
      Nat.factorial (2 * n)
        = (2 * n) * (2 * n - 1) * Nat.factorial (2 * (n - 1)) := by
    have h : 2 * n = 2 * (n - 1) + 2 := by omega
    rw [h]
    simp [Nat.factorial_succ]
    ring
  have hfacden :
      Nat.factorial ((n - 1) - k + 1)
        = (((n - 1) - k + 1) : ℕ) * Nat.factorial ((n - 1) - k) := by
    rw [show (n - 1) - k + 1 = ((n - 1) - k) + 1 by omega]
    simp [Nat.factorial_succ]
  have hden_ne : (↑n - ↑k : ℝ) ≠ 0 := by
    have hkleR : (k : ℝ) ≤ n - 1 := by exact_mod_cast hkle
    nlinarith
  simp [hermiteEvenCoeff, hkle_n, hkle, hsub, hfac_num]
  rw [hfacden]
  field_simp [hden_ne, Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)]
  norm_num [Nat.cast_add, Nat.cast_mul]
  have hcast : (↑(n - 1) - ↑k + 1 : ℝ) = ↑(n - 1 - k) + 1 := by
    rw [Nat.cast_sub hkle]
  rw [hcast]
  have hsign :
      (-1 : ℝ) ^ (n - 1 - k + 1) = -((-1 : ℝ) ^ (n - 1 - k)) := by
    rw [pow_succ]
    ring
  rw [hsign]
  ring

/-- Coefficient recurrence induced by multiplication by `4s-2` in the
scaled Pochhammer basis. -/
private lemma hermiteEvenCoeff_recurrence
    (n k : ℕ) (hn : 1 ≤ n) :
    hermiteEvenCoeff (n + 1) k =
      (if k = 0 then 0 else 4 * hermiteEvenCoeff n (k - 1))
        - (8 * (k : ℝ) + 2) * hermiteEvenCoeff n k
        + (8 * (n : ℝ) * (((2 * n - 1 : ℕ) : ℝ)))
            * hermiteEvenCoeff (n - 1) k := by
  by_cases hk0 : k = 0
  · subst k
    have hB := hermiteEvenCoeff_next_ratio n 0 (Nat.zero_le n)
    have hC := hermiteEvenCoeff_prev_n_ratio n 0 hn (by omega)
    simp only [Nat.sub_zero, Nat.cast_zero, mul_zero, ite_true] at hB hC ⊢
    have hden_ne : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    apply mul_left_cancel₀ hden_ne
    calc
      ((n + 1 : ℕ) : ℝ) * hermiteEvenCoeff (n + 1) 0
          = - ((((2 * n + 2 : ℕ) : ℝ) * (((2 * n + 1 : ℕ) : ℝ)))
              * hermiteEvenCoeff n 0) := hB
      _ = ((n + 1 : ℕ) : ℝ) *
            (-(2 : ℝ) * hermiteEvenCoeff n 0
              + (8 * (n : ℝ) * (((2 * n - 1 : ℕ) : ℝ)))
                  * hermiteEvenCoeff (n - 1) 0) := by
        have hC' :
            (((2 * n : ℕ) : ℝ) * (((2 * n - 1 : ℕ) : ℝ))
              * hermiteEvenCoeff (n - 1) 0)
              = -((n : ℝ) * hermiteEvenCoeff n 0) := by
          linarith [hC]
        have hmul :
            8 * (n : ℝ) * (((2 * n - 1 : ℕ) : ℝ))
                * hermiteEvenCoeff (n - 1) 0
              = 4 * ((((2 * n : ℕ) : ℝ) * (((2 * n - 1 : ℕ) : ℝ))
                * hermiteEvenCoeff (n - 1) 0)) := by
          norm_num [Nat.cast_mul]
          ring
        rw [hmul, hC']
        norm_num [Nat.cast_add, Nat.cast_mul]
        ring_nf
      _ = ((n + 1 : ℕ) : ℝ) *
            (0 - (0 + 2) * hermiteEvenCoeff n 0
              + 8 * (n : ℝ) * (((2 * n - 1 : ℕ) : ℝ))
                  * hermiteEvenCoeff (n - 1) 0) := by
        ring
  · simp only [hk0, if_false]
    by_cases hklenm1 : k ≤ n - 1
    · have hkpos : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk0)
      have hkle : k ≤ n := by omega
      have hA := hermiteEvenCoeff_prev_ratio n k hkpos hkle
      have hB := hermiteEvenCoeff_next_ratio n k hkle
      have hC := hermiteEvenCoeff_prev_n_ratio n k hn hklenm1
      have hden_ne : (((n - k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      have hden_eq : n + 1 - k = n - k + 1 := by omega
      rw [hden_eq] at hB
      -- Clear the common denominator `n-k+1` and reduce to the three ratio lemmas.
      apply mul_left_cancel₀ hden_ne
      calc
        (((n - k + 1 : ℕ) : ℝ)) * hermiteEvenCoeff (n + 1) k
            = - ((((2 * n + 2 : ℕ) : ℝ) * (((2 * n + 1 : ℕ) : ℝ)))
                * hermiteEvenCoeff n k) := hB
        _ = (((n - k + 1 : ℕ) : ℝ)) *
              ((4 * hermiteEvenCoeff n (k - 1))
                - (8 * (k : ℝ) + 2) * hermiteEvenCoeff n k
                + (8 * (n : ℝ) * (((2 * n - 1 : ℕ) : ℝ)))
                    * hermiteEvenCoeff (n - 1) k) := by
          have hC' :
              (((2 * n : ℕ) : ℝ) * (((2 * n - 1 : ℕ) : ℝ))
                * hermiteEvenCoeff (n - 1) k)
                = -(((n - k : ℕ) : ℝ) * hermiteEvenCoeff n k) := by
            linarith [hC]
          have hmul :
              (((n - k + 1 : ℕ) : ℝ))
                  * (8 * (n : ℝ) * (((2 * n - 1 : ℕ) : ℝ))
                    * hermiteEvenCoeff (n - 1) k)
                = (((n - k + 1 : ℕ) : ℝ))
                    * (4 * ((((2 * n : ℕ) : ℝ) * (((2 * n - 1 : ℕ) : ℝ))
                      * hermiteEvenCoeff (n - 1) k))) := by
            norm_num [Nat.cast_mul]
            ring_nf
            left
            trivial
          rw [mul_add, mul_sub, hA, hmul, hC']
          norm_num [Nat.cast_add, Nat.cast_mul]
          rw [Nat.cast_sub hkle]
          have hk2sub : (((2 * k - 1 : ℕ) : ℝ)) = 2 * (k : ℝ) - 1 := by
            rw [Nat.cast_sub (by omega : 1 ≤ 2 * k)]
            norm_num [Nat.cast_mul]
          rw [hk2sub]
          ring_nf
    · -- remaining cases: k = n or k = n+1 or outside support
      by_cases hkle_n : k ≤ n
      · have hkn : k = n := by omega
        subst k
        have hA := hermiteEvenCoeff_prev_ratio n n hn le_rfl
        have hB := hermiteEvenCoeff_next_ratio n n le_rfl
        have hzero : hermiteEvenCoeff (n - 1) n = 0 := by
          simp [hermiteEvenCoeff, show ¬ n ≤ n - 1 by omega]
        have hA' :
            4 * hermiteEvenCoeff n (n - 1)
              = -((((2 * n : ℕ) : ℝ) * (((2 * n - 1 : ℕ) : ℝ)))
                  * hermiteEvenCoeff n n) := by
          simpa [show n - n + 1 = 1 by omega] using hA
        have hB' :
            hermiteEvenCoeff (n + 1) n
              = -((((2 * n + 2 : ℕ) : ℝ) * (((2 * n + 1 : ℕ) : ℝ)))
                  * hermiteEvenCoeff n n) := by
          simpa [show n + 1 - n = 1 by omega] using hB
        rw [hB', hA', hzero]
        norm_num [Nat.cast_add, Nat.cast_mul]
        have h2n1 : (((2 * n - 1 : ℕ) : ℝ)) = 2 * (n : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]
          norm_num [Nat.cast_mul]
        rw [h2n1]
        ring
      · by_cases hkle_np1 : k ≤ n + 1
        · have hkn1 : k = n + 1 := by omega
          subst k
          have hlead_next :
              hermiteEvenCoeff (n + 1) (n + 1) = (2 : ℝ) ^ (2 * (n + 1)) := by
            simp [hermiteEvenCoeff, Nat.factorial_ne_zero]
          have hlead :
              hermiteEvenCoeff n n = (2 : ℝ) ^ (2 * n) := by
            simp [hermiteEvenCoeff, Nat.factorial_ne_zero]
          have hzero_n : hermiteEvenCoeff n (n + 1) = 0 := by
            simp [hermiteEvenCoeff]
          have hzero_prev : hermiteEvenCoeff (n - 1) (n + 1) = 0 := by
            simp [hermiteEvenCoeff, show ¬ n + 1 ≤ n - 1 by omega]
          have hpow : (2 : ℝ) ^ (2 * (n + 1)) = 4 * (2 : ℝ) ^ (2 * n) := by
            have h : 2 * (n + 1) = 2 * n + 2 := by omega
            rw [h, pow_add]
            norm_num
            ring
          have hsub : n + 1 - 1 = n := by omega
          rw [hlead_next, hsub, hlead, hzero_n, hzero_prev, hpow]
          ring
        · have hn1_false : ¬ k ≤ n + 1 := hkle_np1
          have hn_false : ¬ k ≤ n := hkle_n
          have hnm1_false : ¬ k ≤ n - 1 := by omega
          have hkm1_false : ¬ k - 1 ≤ n := by omega
          simp [hermiteEvenCoeff, hn1_false, hn_false, hnm1_false, hkm1_false]

/-- Eval form of `P2nPoly` in the scaled basis. -/
private lemma P2nPoly_eval_sum_scaled (n : ℕ) (s : ℝ) :
    (P2nPoly n).eval s =
      ∑ j ∈ Finset.range (n + 1),
        hermiteEvenCoeff n j * (scaledPochhammerHalfX j).eval s := by
  rw [P2nPoly_eq_sum_scaled]
  simp [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C]

/-- Shift the `k-1` contribution in the scaled Pochhammer basis. -/
private lemma shift_scaled_sum_identity (n : ℕ) (s : ℝ) :
    (∑ x ∈ Finset.range (2 + n),
      (if x = 0 then 0 else hermiteEvenCoeff n (x - 1) * 4)
        * (scaledPochhammerHalfX x).eval s)
      =
    ∑ x ∈ Finset.range (1 + n),
      (s * hermiteEvenCoeff n x * (scaledPochhammerHalfX x).eval s * 4
        + (x : ℝ) * hermiteEvenCoeff n x
            * (scaledPochhammerHalfX x).eval s * 8) := by
  rw [show 2 + n = (1 + n) + 1 by omega]
  rw [Finset.sum_range_succ']
  simp only [if_true, zero_mul]
  rw [add_zero]
  apply Finset.sum_congr rfl
  intro x _
  have hx0 : x + 1 ≠ 0 := by omega
  simp only [hx0, if_false]
  rw [Nat.add_sub_cancel]
  rw [scaledPochhammer_eval_succ]
  ring

/-- Terms involving `hermiteEvenCoeff n` vanish at `x = n + 1`, so a
sum over `range (n+2)` can be shortened to `range (n+1)`. -/
private lemma hermite_sum_extend_one (n : ℕ) (s : ℝ) :
    (∑ x ∈ Finset.range (2 + n),
      ((x : ℝ) * hermiteEvenCoeff n x
          * (scaledPochhammerHalfX x).eval s * 8
        + hermiteEvenCoeff n x * (scaledPochhammerHalfX x).eval s * 2))
      =
    ∑ x ∈ Finset.range (1 + n),
      ((x : ℝ) * hermiteEvenCoeff n x
          * (scaledPochhammerHalfX x).eval s * 8
        + hermiteEvenCoeff n x * (scaledPochhammerHalfX x).eval s * 2) := by
  rw [show 2 + n = (1 + n) + 1 by omega]
  rw [Finset.sum_range_succ]
  simp [hermiteEvenCoeff, show ¬ 1 + n ≤ n by omega]

/-- The `x · h(n,x)` part vanishes at `x = n + 1`. -/
private lemma hermite_x_sum_extend_one (n : ℕ) (s : ℝ) :
    (∑ x ∈ Finset.range (2 + n),
      (x : ℝ) * hermiteEvenCoeff n x
          * (scaledPochhammerHalfX x).eval s * 8)
      =
    ∑ x ∈ Finset.range (1 + n),
      (x : ℝ) * hermiteEvenCoeff n x
          * (scaledPochhammerHalfX x).eval s * 8 := by
  rw [show 2 + n = (1 + n) + 1 by omega]
  rw [Finset.sum_range_succ]
  simp [hermiteEvenCoeff, show ¬ 1 + n ≤ n by omega]

/-- The `h(n,x)` part vanishes at `x = n + 1`. -/
private lemma hermite_const_sum_extend_one (n : ℕ) (s : ℝ) :
    (∑ x ∈ Finset.range (2 + n),
      hermiteEvenCoeff n x * (scaledPochhammerHalfX x).eval s * 2)
      =
    ∑ x ∈ Finset.range (1 + n),
      hermiteEvenCoeff n x * (scaledPochhammerHalfX x).eval s * 2 := by
  rw [show 2 + n = (1 + n) + 1 by omega]
  rw [Finset.sum_range_succ]
  simp [hermiteEvenCoeff, show ¬ 1 + n ≤ n by omega]

set_option linter.flexible false in
/-- Terms involving `hermiteEvenCoeff (n-1)` vanish at `x = n` and
`x = n+1`, so a sum over `range (n+2)` can be shortened to `range n`. -/
private lemma hermite_prev_sum_extend_two (n : ℕ) (hn : 1 ≤ n) (s : ℝ) :
    (∑ x ∈ Finset.range (2 + n),
      (n : ℝ) * (((n * 2 - 1 : ℕ) : ℝ)) * hermiteEvenCoeff (n - 1) x
          * (scaledPochhammerHalfX x).eval s * 8)
      =
    ∑ x ∈ Finset.range (1 + (n - 1)),
      (n : ℝ) * (((n * 2 - 1 : ℕ) : ℝ)) * hermiteEvenCoeff (n - 1) x
          * (scaledPochhammerHalfX x).eval s * 8 := by
  have hr : 1 + (n - 1) = n := by omega
  rw [hr]
  rw [show 2 + n = (n + 1) + 1 by omega]
  rw [Finset.sum_range_succ]
  simp [hermiteEvenCoeff, show ¬ n + 1 ≤ n - 1 by omega]
  rw [Finset.sum_range_succ]
  simp [show ¬ n ≤ n - 1 by omega]

/-- **Three-term recurrence** for `P2nPoly` (eval form):
`P_{n+1}(s) = (4s − 2) · P_n(s) + 8n(2n − 1) · P_{n−1}(s)`
for `n ≥ 1`. -/
theorem P2nPoly_recurrence_eval (n : ℕ) (hn : 1 ≤ n) (s : ℝ) :
    (P2nPoly (n + 1)).eval s
      = (4 * s - 2) * (P2nPoly n).eval s
        + (8 * (n : ℝ) * ((2 * n - 1 : ℕ) : ℝ))
            * (P2nPoly (n - 1)).eval s := by
  rw [P2nPoly_eval_sum_scaled (n + 1) s,
      P2nPoly_eval_sum_scaled n s,
      P2nPoly_eval_sum_scaled (n - 1) s]
  simp only [Finset.mul_sum]
  -- First rewrite the left-hand coefficients by the coefficient recurrence.
  rw [Finset.sum_congr rfl (fun j _ => by
    rw [hermiteEvenCoeff_recurrence n j hn])]
  ring_nf
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [shift_scaled_sum_identity n s,
      hermite_prev_sum_extend_two n hn s]
  rw [hermite_x_sum_extend_one n s, hermite_const_sum_extend_one n s]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring_nf

/-- **Reflection symmetry** of the general `P2nPoly` (proved).

For every `n`, `P2nPoly n .eval (1 − s) = (−1)^n · P2nPoly n .eval s`.
The proof is by two-step induction, the inductive step uses
`P2nPoly_recurrence_eval`. -/
theorem P2nPoly_reflect (n : ℕ) (s : ℝ) :
    (P2nPoly n).eval (1 - s)
      = (-1 : ℝ) ^ n * (P2nPoly n).eval s := by
  induction n using Nat.twoStepInduction with
  | zero =>
      -- n = 0: P_0 = 1, both sides equal 1.
      simp [P2nPoly, hermiteEvenCoeff,
            pochhammerHalfX, ascPochhammer_zero]
  | one =>
      -- n = 1: P_1(s) = 4s - 2; P_1(1-s) = -P_1(s).
      simp [P2nPoly, hermiteEvenCoeff,
            pochhammerHalfX, Nat.factorial,
            Finset.sum_range_succ, ascPochhammer_zero]
      ring
  | more n ih_n ih_succ =>
      -- target n+2; apply recurrence at n+1.
      have hpos : 1 ≤ n + 1 := by omega
      have hL := P2nPoly_recurrence_eval (n + 1) hpos (1 - s)
      have hR := P2nPoly_recurrence_eval (n + 1) hpos s
      -- (n + 1) - 1 = n.
      have hsub : (n + 1) - 1 = n := by omega
      rw [hsub] at hL hR
      -- Substitute IH values.
      rw [hL, ih_succ, ih_n]
      rw [hR]
      -- Sign manipulation: (−1)^(n+2) = (−1)^n.
      have hsign : (-1 : ℝ) ^ (n + 2) = (-1 : ℝ) ^ n := by
        rw [pow_add]; ring
      rw [hsign]
      ring

/-- The general reflection-symmetry conjecture is now a theorem. -/
theorem P2nPolyReflectConjecture_proved : P2nPolyReflectConjecture :=
  P2nPoly_reflect

end GaussianWhoWhere
