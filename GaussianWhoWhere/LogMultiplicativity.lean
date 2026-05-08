import GaussianWhoWhere.PolynomialRigidity

/-!
# Sampled-translation rigidity (Level 1, abstract core)

The bridge from "Q satisfies the translation factorization on a single
injective sequence of sample points" up to "Q satisfies the translation
factorization as a polynomial identity" — and hence (combined with
`Q(0) = 1` and `a ≠ 0`) up to `Q = 1` via Level 0 rigidity.

This file is deliberately *abstract*: it does not mention `Real.log`,
`Nat.Coprime`, or any number-theoretic structure. The intended later
instantiation `u n := Real.log (2*n + 1)` together with multiplicativity
`Q(log m·n) = Q(log m) · Q(log n)` lives in a separate file.
-/

noncomputable section

namespace GaussianWhoWhere

open Polynomial

/-- If the translation relation `Q(u n + a) = Q(a) · Q(u n)` holds on an
infinite injective sequence of sample points `u : ℕ → ℝ`, then it lifts
to a polynomial identity:

`Q.comp (X + C a) = C (Q.eval a) * Q`.

Proof: the difference `R := Q.comp (X + C a) − C (Q.eval a) · Q`
vanishes at every `u n`. Injectivity of `u` makes this an infinite root
set, and `Polynomial.eq_zero_of_infinite_isRoot` forces `R = 0`. -/
lemma polynomial_translation_identity_of_infinite_eval
    (Q : Polynomial ℝ) (a : ℝ) (u : ℕ → ℝ)
    (hinj : Function.Injective u)
    (hvals : ∀ n : ℕ, Q.eval (u n + a) = Q.eval a * Q.eval (u n)) :
    Q.comp (Polynomial.X + Polynomial.C a)
      = Polynomial.C (Q.eval a) * Q := by
  -- Let R be the difference of the two sides.
  set R : Polynomial ℝ :=
    Q.comp (Polynomial.X + Polynomial.C a)
      - Polynomial.C (Q.eval a) * Q with hR
  -- Each u n is a root of R.
  have hroots : ∀ n : ℕ, u n ∈ {x : ℝ | R.IsRoot x} := by
    intro n
    change R.IsRoot (u n)
    rw [Polynomial.IsRoot.def]
    change Polynomial.eval (u n) R = 0
    rw [hR, Polynomial.eval_sub, Polynomial.eval_mul,
        Polynomial.eval_comp, Polynomial.eval_add,
        Polynomial.eval_X, Polynomial.eval_C,
        Polynomial.eval_C, hvals n]
    ring
  -- Injectivity of u promotes this to an infinite root set.
  have hinf : {x : ℝ | R.IsRoot x}.Infinite :=
    Set.infinite_of_injective_forall_mem hinj hroots
  -- A polynomial with infinitely many roots is zero.
  have hRzero : R = 0 :=
    Polynomial.eq_zero_of_infinite_isRoot R hinf
  -- Hence the two sides agree.
  exact sub_eq_zero.mp hRzero

/-- Abstract Level 1 rigidity.

If the translation relation holds on an infinite injective sequence of
sample points and the Level 0 boundary conditions `Q.eval 0 = 1`,
`a ≠ 0` are met, then `Q = 1`. -/
theorem polynomial_rigidity_of_infinite_sampled_translation
    (Q : Polynomial ℝ) (a : ℝ) (u : ℕ → ℝ)
    (ha : a ≠ 0)
    (hQ0 : Q.eval 0 = 1)
    (hinj : Function.Injective u)
    (hvals : ∀ n : ℕ, Q.eval (u n + a) = Q.eval a * Q.eval (u n)) :
    Q = 1 := by
  -- Lift sampled translation to polynomial identity.
  have hid :
      Q.comp (Polynomial.X + Polynomial.C a)
        = Polynomial.C (Q.eval a) * Q :=
    polynomial_translation_identity_of_infinite_eval Q a u hinj hvals
  -- Convert back to pointwise translation hypothesis at every x.
  have htrans : ∀ x : ℝ, Q.eval (x + a) = Q.eval a * Q.eval x := by
    intro x
    have := congrArg (Polynomial.eval x) hid
    simpa [Polynomial.eval_comp] using this
  -- Apply Level 0 rigidity.
  exact polynomial_translation_rigidity Q a ha hQ0 htrans

/-! ## Concrete instantiation: odd-log sampling

The intended downstream use of the abstract Level 1 lemma supplies
sample points `u n := Real.log (2n + 1)`. We record the basic
injectivity here and the immediate specialization of the rigidity
theorem. The supply of `hvals` (typically from a coprime-multiplicativity
argument) is left to the caller. -/

/-- Sample sequence `u n = log (2n + 1)`. -/
def oddLogSample (n : ℕ) : ℝ :=
  Real.log (((2 * n + 1 : ℕ) : ℝ))

theorem oddLogSample_injective : Function.Injective oddLogSample := by
  intro m n h
  have hm : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by positivity
  have hn : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by positivity
  have harg : ((2 * m + 1 : ℕ) : ℝ) = ((2 * n + 1 : ℕ) : ℝ) :=
    Real.log_injOn_pos (Set.mem_Ioi.mpr hm) (Set.mem_Ioi.mpr hn) h
  have hnat : 2 * m + 1 = 2 * n + 1 := by exact_mod_cast harg
  omega

/-- Specialization of `polynomial_rigidity_of_infinite_sampled_translation`
to the odd-log sample sequence `u n = log (2n + 1)`. -/
theorem polynomial_rigidity_of_odd_log_sampled_translation
    (Q : Polynomial ℝ) (a : ℝ)
    (ha : a ≠ 0)
    (hQ0 : Q.eval 0 = 1)
    (hvals : ∀ n : ℕ,
      Q.eval (oddLogSample n + a) = Q.eval a * Q.eval (oddLogSample n)) :
    Q = 1 :=
  polynomial_rigidity_of_infinite_sampled_translation
    Q a oddLogSample ha hQ0 oddLogSample_injective hvals

end GaussianWhoWhere
