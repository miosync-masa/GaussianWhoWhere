# GaussianWhoWhere

Lean formalization project for the finite Hermite-Pochhammer core of the
Who/Where decomposition of zeta-type structures.

## Status

> **Every Lean file in this repository is `sorry`-free and `admit`-free.**

The current headline result is

```text
finite_general_uniqueness :
  ∀ (K : ℕ) (c : Fin K → ℝ),
    (∀ x y : ℝ,
      (QFinitePoly K c).eval (x + y)
        = (QFinitePoly K c).eval x * (QFinitePoly K c).eval y)
    → ∀ k : Fin K, c k = 0
```

where

```text
QFinitePoly K c
  = 1 + Σ (k : Fin K), (c k) · P_{4(k+1)}(x)     -- as a real polynomial
```

is the **arbitrary finite Hermite–Pochhammer truncation polynomial**
ranging over `P₄, P₈, P₁₂, …, P_{4K}`. The theorem says that any such
truncation satisfying the Cauchy multiplicative equation collapses
identically: every coefficient `c_k = 0`. The proof reduces to the
Level 0 polynomial translation rigidity theorem via the leading
coefficient `(P2nPoly n).leadingCoeff = 2^(2n)` and a descending
induction on `K`.

In particular this generalizes — and supersedes — the earlier
`finite_concrete_uniqueness_P16` (which handled only the truncation up
to `P₁₆`). The full statement and proof live in
[`GaussianWhoWhere/FiniteGeneralUniqueness.lean`](GaussianWhoWhere/FiniteGeneralUniqueness.lean).

## Core idea

- Multiplicativity identifies the arithmetic object (`who`).
- Functional symmetry determines the zero-geometry axis (`where`).
- In the finite Hermite-Pochhammer deformation family, the Gaussian kernel
  is the unique point where both coexist.

## Formalization levels

- Level 0: polynomial translation rigidity
- Level 1 (abstract core): rigidity from a single injective sequence of
  sample points; concrete odd-log specialization
- Level 2: finite Hermite-Pochhammer uniqueness up to `P₁₆`
- Level 2G: arbitrary finite Hermite-Pochhammer uniqueness up to `P_{4K}`
- Level 3: concrete verification of `P₄/P₈/P₁₂/P₁₆`, the finite
  Hermite-Pochhammer generation, and the **general** `P_{2n}`
  construction with its three-term recurrence and reflection symmetry
- Level 4: abstract Bridge/Who/Where predicates (type structure only;
  interpretive content lives in the paper)

## Formalized results

All results below are proved in Lean with **no `sorry`**.

### Level 0 — [`GaussianWhoWhere/PolynomialRigidity.lean`](GaussianWhoWhere/PolynomialRigidity.lean)

- `polynomial_translation_rigidity`:
  a real polynomial `Q` satisfying `Q(x + a) = Q(a) · Q(x)` for all `x`,
  with `a ≠ 0` and `Q(0) = 1`, is identically `1`.

  Helper lemmas (also exposed):
  `polynomial_translation_identity`,
  `polynomial_eq_one_of_natDegree_zero`,
  `polynomial_translation_eval_eq_one_of_pos_natDegree`,
  `polynomial_natDegree_zero_of_comp_X_add_C_eq_self`.

### Level 1 — [`GaussianWhoWhere/LogMultiplicativity.lean`](GaussianWhoWhere/LogMultiplicativity.lean)

**Abstract core.**

- `polynomial_translation_identity_of_infinite_eval`:
  the translation relation on a single injective sequence of sample
  points lifts to the polynomial identity
  `Q.comp (X + C a) = C (Q.eval a) · Q`.

- `polynomial_rigidity_of_infinite_sampled_translation`:
  combined with `Q(0) = 1` and `a ≠ 0`, the Level 0 conclusion holds.

**Concrete odd-log specialization.**

- `oddLogSample n := Real.log (2n + 1)` together with
  `oddLogSample_injective`.
- `polynomial_rigidity_of_odd_log_sampled_translation`:
  the abstract Level 1 theorem instantiated at `u n = log (2n + 1)`.
  The supply of `hvals` (typically from a coprime-multiplicativity
  argument on the odd integers) is left to downstream callers.

### Level 2 — [`GaussianWhoWhere/FiniteUniqueness.lean`](GaussianWhoWhere/FiniteUniqueness.lean)

- `finite_concrete_uniqueness_P16`:
  if the truncated deformation
  `Q4 c4 c8 c12 c16 (x) = 1 + c4·P₄(x) + c8·P₈(x) + c12·P₁₂(x) + c16·P₁₆(x)`
  is multiplicative under addition, then `c4 = c8 = c12 = c16 = 0`.

  Polynomial-layer building blocks:
  `Q4Poly_eq_one_of_translation`,
  `coeffs_zero_of_Q4Poly_eq_one`,
  `finite_concrete_uniqueness_P16_of_translation`.

### Level 2G — [`GaussianWhoWhere/FiniteGeneralUniqueness.lean`](GaussianWhoWhere/FiniteGeneralUniqueness.lean)

The Level 2 result extended to **arbitrary finite truncation `K`**:

  `Q_K(x) := 1 + Σ_{k = 0}^{K - 1} c_k · P_{4(k+1)}(x)`

(the `k`-th summand uses `P2nPoly (2(k+1))`, ranging over `P₄, P₈,
P₁₂, …, P_{4K}`).

- `coeff_P2nPoly_top`: `(P2nPoly n).coeff n = 2^(2n)`.
- `natDegree_P2nPoly`: `(P2nPoly n).natDegree = n`.
- `leadingCoeff_P2nPoly`: `(P2nPoly n).leadingCoeff = 2^(2n)`.
- `QFinitePoly K c`: the truncation polynomial.
- `QFinitePoly_eq_one_of_translation`: a single-step translation
  rigidity wrapper around `polynomial_translation_rigidity`.
- `coeffs_zero_of_QFinitePoly_eq_one`: from `Q_K = 1` (as a real
  polynomial), descending induction on `K` peels off the highest
  coefficient using the leading coefficient `2^(2(2k+2))`, yielding
  `c_k = 0` for every `k`.
- `finite_general_uniqueness_of_translation`: the translation-form
  conclusion combining the wrapper and the peeling.
- `finite_general_uniqueness`: the full Cauchy multiplicativity
  conclusion, handling both `Q(0) = 1` (rigidity at `a = 1`) and
  `Q(0) = 0` (collapse to the zero polynomial via the same peeling).

### Level 3 — [`GaussianWhoWhere/ConcretePolynomials.lean`](GaussianWhoWhere/ConcretePolynomials.lean) and [`HermitePochhammer.lean`](GaussianWhoWhere/HermitePochhammer.lean)

**Concrete polynomials.**

- Symmetry: `P4_symm`, `P8_symm`, `P12_symm`, `P16_symm`
  (each `P_k(s) = P_k(1 − s)`).
- Non-additivity: `P4_not_additive`, …, `P16_not_additive`.

**Finite Hermite-Pochhammer generation.**

- For `k ∈ {4, 8, 12, 16}`, `hermitePochhammer_Hk_eq_Pk` proves
  `P_kGen s = P_k s`, where `P_kGen` is constructed from explicit
  Hermite-style coefficient sequences `H4Coeff`, `H8Coeff`,
  `H12Coeff`, `H16Coeff` via the expansion
  `P_{2n}(s) = Σ_j h_j · 2^j · (s/2)_j`.

**General `P_{2n}` construction.**

- `halfX`, `pochhammerHalfX`, `eval_pochhammerHalfX`:
  `(s/2)_j` packaged as a `Polynomial ℝ` via Mathlib's
  `ascPochhammer` composed with `(1/2) · X`, with a bridge to the
  project-local `risingFactorial`.

- `hermiteEvenCoeff n j`: closed-form physicists'-Hermite even
  coefficient `(−1)^(n−j) · (2n)!/((n−j)!(2j)!) · 2^(2j)`. Coincides
  with the explicit `H_kCoeff` at the four concrete values
  `n ∈ {2, 4, 6, 8}` (theorems
  `hermiteEvenCoeff_two_eq_H4Coeff`,
  `hermiteEvenCoeff_four_eq_H8Coeff`,
  `hermiteEvenCoeff_six_eq_H12Coeff`,
  `hermiteEvenCoeff_eight_eq_H16Coeff`).

- `P2nPoly n : Polynomial ℝ`, the general `P_{2n}` polynomial
  defined uniformly via `hermiteEvenCoeff` and `pochhammerHalfX`.

- `P2nPoly_two_eval_eq_P4`, …, `P2nPoly_eight_eval_eq_P16`:
  the general construction matches the concrete `P_k` at
  `n = 2, 4, 6, 8`.

- `P2nPoly_two_symm`, …, `P2nPoly_eight_symm`: reflection symmetry
  inherited from the concrete `P_k_symm` at the four sample values.

**General three-term recurrence and reflection.**

- `scaledPochhammerHalfX`, `eval_scaledPochhammerHalfX`,
  `P2nPoly_eq_sum_scaled`,
  `scaledPochhammer_eval_succ`,
  `four_s_sub_two_mul_scaledPochhammer_eval`:
  scaffolding for the basis-level multiplication formula.

- `P2nPoly_recurrence_eval` (for `n ≥ 1`):
  `(P2nPoly (n+1)).eval s = (4s − 2) · (P2nPoly n).eval s
                              + 8 n (2n − 1) · (P2nPoly (n−1)).eval s`.

- `P2nPoly_reflect` (for **all** `n`):
  `(P2nPoly n).eval (1 − s) = (−1)^n · (P2nPoly n).eval s`.

- `P2nPolyReflectConjecture_proved`: the reflection symmetry packaged
  at the original `Prop` form, now a theorem.

### Level 4 — [`GaussianWhoWhere/BridgeStructure.lean`](GaussianWhoWhere/BridgeStructure.lean)

Type-level scaffolding only. No critical-line implication is
asserted at this layer.

- `ReflectedZeroSymmetry`, `CriticalLineProperty`
- `FunctionalSymmetry`, `ArithmeticIdentity`, `WhoWhereCompatible`
- `where_gives_reflected_zero_geometry`

### Infinite Coupler — [`GaussianWhoWhere/InfiniteCoupler.lean`](GaussianWhoWhere/InfiniteCoupler.lean)

This file does **not** formalize Jensen / Cartwright zero-density
theory. Instead, it isolates the analytic inputs needed for the
infinite Hermite–Pochhammer extension and proves the abstract
*coupler* theorem.

- `HPftLike Q`: placeholder for the analytic class (entire,
  finite exponential type, closed under translations).
- `InfiniteWho Q`: data-bearing structure recording two
  simultaneous translation eigen-relations along incommensurable
  shifts (`shift2`, `shift3` with eigenvalues `A2`, `A3`,
  intended `log 2` / `log 3`).
- `InfiniteWhere Q`: reflection symmetry `Q(1 − z) = Q(z)`.
- `TwoTranslationExponentialRigidity Q`: analytic input A —
  HP_ft + Who ⇒ exponential survivor `Q(z) = exp(c · z)`.
- `WhereKillsExponential Q`: analytic input B — Where eliminates
  the exponential, forcing `Q ≡ 1`.
- `infinite_who_where_rigidity`:
  composition of the two analytic inputs: under all four
  hypotheses, `Q ≡ 1`. This is a Lean-level skeleton for the
  infinite Bridge C argument; the analytic content is supplied
  downstream as instances of `TwoTranslationExponentialRigidity`
  and `WhereKillsExponential`.

### Infinite L3 layer — [`GaussianWhoWhere/Infinite/`](GaussianWhoWhere/Infinite/)

A factored interface stack feeding the infinite Bridge C coupler.
Each layer is no-sorry; analytic inputs (Jensen / Cartwright /
zero-density theory) are not formalized — they are isolated as
`Prop`-valued bundles so they can be supplied later as instances.

| Layer | File | Role |
|---|---|---|
| 1 | [`FiniteExponentialType.lean`](GaussianWhoWhere/Infinite/FiniteExponentialType.lean) | Closure properties of `FiniteExpType F`: const, translate, const_mul, add, sub. |
| 2 | [`TranslationDefect.lean`](GaussianWhoWhere/Infinite/TranslationDefect.lean) | The defect `R_{a,A}(z) := Q(z + a) − A · Q(z)` stays in the class. |
| 3 | [`ZeroDensityInterface.lean`](GaussianWhoWhere/Infinite/ZeroDensityInterface.lean) | `SampledZeros` of the defect → defect ≡ 0 → global eigen-relation. |
| 4 | [`ArithmeticSamples.lean`](GaussianWhoWhere/Infinite/ArithmeticSamples.lean) | Who-side single sampled input → global eigen-relation. |
| 5 | [`TwoShiftCoupler.lean`](GaussianWhoWhere/Infinite/TwoShiftCoupler.lean) | Two who-inputs (incommensurable shifts) → global pair. |
| 6 | [`ExponentialSurvivorInterface.lean`](GaussianWhoWhere/Infinite/ExponentialSurvivorInterface.lean) | Incommensurable global pair → `Q(z) = exp(c · z)`. |
| 7 | [`WhereKillsExponential.lean`](GaussianWhoWhere/Infinite/WhereKillsExponential.lean) | Pipeline applications: where + survivor ⇒ `Q ≡ 1`. |
| 8 | [`InfiniteRigidity.lean`](GaussianWhoWhere/Infinite/InfiniteRigidity.lean) | Top-level DAG (see below). |

#### Top-level infinite rigidity ([`InfiniteRigidity.lean`](GaussianWhoWhere/Infinite/InfiniteRigidity.lean))

- `infinite_rigidity_from_sampled_who_where`:
  packages the full interface-level infinite DAG. Given finite
  exponential type, zero-density uniqueness, two incommensurable
  sampled who-inputs, the exponential-survivor principle, the
  where-kills-exponential principle, and the where symmetry, we
  conclude `Q ≡ 1`.

- `infinite_rigidity_from_global_who_where`:
  same theorem starting from already-global incommensurable
  translation eigen-relations (after the zero-density step).

- `bridgeC_infinite_coupler`:
  interpretation-flavored alias of the sampled-input theorem,
  emphasizing the Bridge C reading.

These infinite theorems do **not** prove Jensen / Cartwright
zero-density theory. They isolate the analytic inputs and formalize
the logical coupler skeleton.

## Theorem map

For a single navigable index of every result above (with `#check`
output of each signature), open
[`GaussianWhoWhere/TheoremMap.lean`](GaussianWhoWhere/TheoremMap.lean).

## Build

```sh
lake exe cache get   # fetch mathlib build cache
lake build
```

Per-file build:

```sh
lake build GaussianWhoWhere.ConcretePolynomials
```

Single-file check (no full build, useful during development):

```sh
lake env lean GaussianWhoWhere/PolynomialRigidity.lean
```

## Verifying `sorry`-freeness

```sh
rg "sorry|admit" GaussianWhoWhere/
```

This should produce no output.
