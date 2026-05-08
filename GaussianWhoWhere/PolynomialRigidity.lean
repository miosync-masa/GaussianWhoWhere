import Mathlib

/-!
# Polynomial translation rigidity (Level 0)

The algebraic core of finite Gaussian who/where uniqueness:
a real polynomial whose translation by a nonzero step factors as
`Q(x + a) = Q(a) * Q(x)`, with `Q(0) = 1`, must be the constant `1`.

## Proof strategy (to be filled in)

1. Suppose `degree Q = d ≥ 1`.
2. Compare leading coefficients of `Q(x + a)` and `Q(a) * Q(x)`:
   the `x^d` coefficient on both sides forces `Q(a) = 1`.
3. Compare the `x^(d-1)` coefficient:
   - LHS contributes `d * a * leadingCoeff Q` from the binomial expansion;
   - RHS contributes nothing extra because `Q(a) = 1`.
4. Hence `d * a * leadingCoeff Q = 0`. Since `d > 0`, `a ≠ 0`, and
   `leadingCoeff Q ≠ 0`, this is a contradiction.
5. Therefore `degree Q = 0`. Combined with `Q(0) = 1`, we get `Q = 1`.

The intended Mathlib tools are `Polynomial.leadingCoeff`,
`Polynomial.natDegree`, `Polynomial.coeff_add`, and
`Polynomial.coeff_comp` (or direct manipulation via `Polynomial.eval`).
-/

noncomputable section

namespace GaussianWhoWhere

open Polynomial

/-- Helper: the translation hypothesis lifts from values to a polynomial identity. -/
lemma polynomial_translation_identity
    (Q : Polynomial ℝ) (a : ℝ)
    (htrans : ∀ x : ℝ, Q.eval (x + a) = Q.eval a * Q.eval x) :
    Q.comp (Polynomial.X + Polynomial.C a) = Polynomial.C (Q.eval a) * Q := by
  apply Polynomial.funext
  intro x
  simp [Polynomial.eval_comp, htrans x]

/-- Constant case: a real polynomial of `natDegree 0` whose value at `0` is
`1` is the constant polynomial `1`. -/
lemma polynomial_eq_one_of_natDegree_zero
    (Q : Polynomial ℝ)
    (hdeg : Q.natDegree = 0)
    (hQ0 : Q.eval 0 = 1) :
    Q = 1 := by
  have hC : Q = Polynomial.C (Q.coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have hcoeff : Q.coeff 0 = 1 := by
    simpa [Polynomial.coeff_zero_eq_eval_zero] using hQ0
  calc
    Q = Polynomial.C (Q.coeff 0) := hC
    _ = Polynomial.C 1 := by rw [hcoeff]
    _ = 1 := by simp

/-- Nonconstant case (leading-coefficient comparison): from the polynomial
identity `Q.comp (X + C a) = C (Q.eval a) * Q` and positivity of
`Q.natDegree`, comparing leading coefficients forces `Q.eval a = 1`. -/
lemma polynomial_translation_eval_eq_one_of_pos_natDegree
    (Q : Polynomial ℝ) (a : ℝ)
    (hpos : 0 < Q.natDegree)
    (hid :
      Q.comp (Polynomial.X + Polynomial.C a)
        = Polynomial.C (Q.eval a) * Q) :
    Q.eval a = 1 := by
  have hQne : Q ≠ 0 := fun hQ0 => by
    rw [hQ0, Polynomial.natDegree_zero] at hpos
    exact (lt_irrefl 0) hpos
  have hlcQ : Q.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hQne
  -- natDegree of (X + C a) is 1, hence ≠ 0.
  have hdegXa : (Polynomial.X + Polynomial.C a).natDegree ≠ 0 := by
    rw [Polynomial.natDegree_X_add_C]; exact one_ne_zero
  -- LHS leading coefficient.
  have hLHS :
      (Q.comp (Polynomial.X + Polynomial.C a)).leadingCoeff
        = Q.leadingCoeff := by
    rw [Polynomial.leadingCoeff_comp hdegXa,
        Polynomial.leadingCoeff_X_add_C, one_pow, mul_one]
  -- RHS leading coefficient.
  -- RHS via leadingCoeff_mul (NoZeroDivisors on ℝ).
  have hRHS :
      (Polynomial.C (Q.eval a) * Q).leadingCoeff
        = Q.eval a * Q.leadingCoeff := by
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C]
  -- Combine.
  have hEq :
      Q.leadingCoeff = Q.eval a * Q.leadingCoeff := by
    have := congrArg Polynomial.leadingCoeff hid
    rw [hLHS, hRHS] at this
    exact this
  -- Cancel Q.leadingCoeff (nonzero).
  have : (1 : ℝ) * Q.leadingCoeff = Q.eval a * Q.leadingCoeff := by
    simpa using hEq
  exact (mul_right_cancel₀ hlcQ this).symm

/-- Periodicity-implies-constant lemma.

If `Q.comp (X + C a) = Q` (i.e. `Q` is invariant under translation by `a`)
and `a ≠ 0`, then `Q` has `natDegree = 0`. The proof uses the
infinite-roots criterion `Polynomial.eq_zero_of_infinite_isRoot`: the
auxiliary polynomial `R := Q - C (Q.eval 0)` vanishes at every multiple
`n · a`, and the map `n ↦ n · a` is injective on `ℕ`. -/
lemma polynomial_natDegree_zero_of_comp_X_add_C_eq_self
    (Q : Polynomial ℝ) (a : ℝ)
    (ha : a ≠ 0)
    (hper : Q.comp (Polynomial.X + Polynomial.C a) = Q) :
    Q.natDegree = 0 := by
  -- Periodicity at the value level.
  have hper_val : ∀ x : ℝ, Q.eval (x + a) = Q.eval x := by
    intro x
    have := congrArg (Polynomial.eval x) hper
    simpa [Polynomial.eval_comp] using this
  -- By induction, Q.eval (n • a) = Q.eval 0 for all n : ℕ.
  have hper_nat : ∀ n : ℕ, Q.eval ((n : ℝ) * a) = Q.eval 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have : Q.eval (((n : ℝ) * a) + a) = Q.eval ((n : ℝ) * a) :=
          hper_val ((n : ℝ) * a)
        have hcast : ((n + 1 : ℕ) : ℝ) * a = ((n : ℝ) * a) + a := by
          push_cast; ring
        rw [hcast, this, ih]
  -- The auxiliary polynomial R := Q - C (Q.eval 0).
  set R : Polynomial ℝ := Q - Polynomial.C (Q.eval 0) with hR
  -- R has infinitely many roots, namely n • a for all n : ℕ.
  have hinj : Function.Injective (fun n : ℕ => (n : ℝ) * a) := by
    intro m n hmn
    have : (m : ℝ) = (n : ℝ) := by
      have := hmn
      exact mul_right_cancel₀ ha this
    exact_mod_cast this
  have hroots : ∀ n : ℕ, ((n : ℝ) * a) ∈ {x : ℝ | R.IsRoot x} := by
    intro n
    change R.IsRoot ((n : ℝ) * a)
    rw [Polynomial.IsRoot.def]
    change Polynomial.eval ((n : ℝ) * a) R = 0
    rw [hR, Polynomial.eval_sub, Polynomial.eval_C, hper_nat n, sub_self]
  have hinf : {x : ℝ | R.IsRoot x}.Infinite :=
    Set.infinite_of_injective_forall_mem hinj hroots
  have hRzero : R = 0 := Polynomial.eq_zero_of_infinite_isRoot R hinf
  -- From R = 0, Q is the constant polynomial C (Q.eval 0).
  set c : ℝ := Q.eval 0 with hc
  have hQ_eq_C : Q = Polynomial.C c :=
    sub_eq_zero.mp hRzero
  -- natDegree of a constant polynomial is 0.
  rw [hQ_eq_C, Polynomial.natDegree_C]

/-- Core polynomial rigidity lemma.

If a real polynomial `Q` satisfies `Q(x + a) = Q(a) * Q(x)` for all `x`,
with `a ≠ 0` and `Q(0) = 1`, then `Q` is the constant polynomial `1`.

This is the algebraic core of finite Gaussian who/where uniqueness. -/
theorem polynomial_translation_rigidity
    (Q : Polynomial ℝ) (a : ℝ)
    (ha : a ≠ 0)
    (hQ0 : Q.eval 0 = 1)
    (htrans : ∀ x : ℝ, Q.eval (x + a) = Q.eval a * Q.eval x) :
    Q = 1 := by
  by_cases hdeg : Q.natDegree = 0
  · exact polynomial_eq_one_of_natDegree_zero Q hdeg hQ0
  · have hpos : 0 < Q.natDegree := Nat.pos_of_ne_zero hdeg
    have hid :
        Q.comp (Polynomial.X + Polynomial.C a)
          = Polynomial.C (Q.eval a) * Q :=
      polynomial_translation_identity Q a htrans
    have hQa : Q.eval a = 1 :=
      polynomial_translation_eval_eq_one_of_pos_natDegree Q a hpos hid
    have hper : Q.comp (Polynomial.X + Polynomial.C a) = Q := by
      calc
        Q.comp (Polynomial.X + Polynomial.C a)
            = Polynomial.C (Q.eval a) * Q := hid
        _ = Polynomial.C 1 * Q := by rw [hQa]
        _ = Q := by simp
    have hdeg0 : Q.natDegree = 0 :=
      polynomial_natDegree_zero_of_comp_X_add_C_eq_self Q a ha hper
    exact absurd hdeg0 hdeg

end GaussianWhoWhere
