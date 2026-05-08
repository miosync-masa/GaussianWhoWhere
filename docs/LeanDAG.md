# Lean DAG

A file-by-file map of the `GaussianWhoWhere` Lean development:
each file's responsibility, key definitions, key theorems, upstream
dependencies, and downstream consumers. The aim is to make the
formal development legible to readers and to future contributors —
and to provide an appendix-ready cross-reference for the paper.

The whole development is `sorry` / `admit`-free; the only intentional
analytic gap is a single named socket
`JensenCartwrightLinearZeroBound`, kept explicit by design (see §4).

---

## 0. Finite Core

The arbitrary-`K` finite Hermite–Pochhammer rigidity theorem.
Self-contained, no analytic interfaces.

### `GaussianWhoWhere/Basic.lean`
* **Role.** Project header / placeholder.
* **Consumed by.** Every downstream file (transitively, via the
  `GaussianWhoWhere` namespace).

### `GaussianWhoWhere/ConcretePolynomials.lean`
* **Role.** Concrete `P_4, P_8, P_{12}, P_{16}` and their polynomial
  versions `P_kPoly`.
* **Definitions.** `P4`, `P8`, `P12`, `P16` (real-valued), `P4Poly`,
  `P8Poly`, `P12Poly`, `P16Poly` (`Polynomial ℝ`).
* **Theorems.** `P_k_symm` (reflection `P_k(s) = P_k(1 − s)`),
  `P_k_not_additive`, `eval_P_kPoly` (bridge between value-level and
  polynomial-level).
* **Consumed by.** `HermitePochhammer.lean`, `FiniteUniqueness.lean`,
  `FiniteGeneralUniqueness.lean`.

### `GaussianWhoWhere/PolynomialRigidity.lean`
* **Role.** **Level 0** — algebraic core of finite who/where uniqueness.
* **Theorems.** `polynomial_translation_rigidity` (a real polynomial
  satisfying `Q(x + a) = Q(a) · Q(x)` with `a ≠ 0`, `Q(0) = 1` is
  identically `1`).
* **Helpers.** `polynomial_translation_identity`,
  `polynomial_eq_one_of_natDegree_zero`,
  `polynomial_translation_eval_eq_one_of_pos_natDegree`,
  `polynomial_natDegree_zero_of_comp_X_add_C_eq_self` (the closing
  step uses the infinite-roots criterion via
  `Polynomial.eq_zero_of_infinite_isRoot`).
* **Consumed by.** `FiniteUniqueness.lean`,
  `FiniteGeneralUniqueness.lean`, `LogMultiplicativity.lean`.

### `GaussianWhoWhere/HermitePochhammer.lean`
* **Role.** Generation of `P_{2n}` from Hermite–Pochhammer expansion;
  general `P2nPoly`, three-term recurrence, reflection symmetry.
* **Definitions.** `risingFactorial`, `hermitePochhammerOfCoeffs`,
  `H_kCoeff` for `k ∈ {4, 8, 12, 16}`, `P_kGen`, `halfX`,
  `pochhammerHalfX`, `hermiteEvenCoeff`, `P2nPoly`,
  `scaledPochhammerHalfX`.
* **Theorems.** `hermitePochhammer_Hk_eq_Pk` (4 versions),
  `P2nPoly_*_eval_eq_P_k`, `P2nPoly_*_symm`,
  `P2nPoly_recurrence_eval`, `P2nPoly_reflect`,
  `P2nPolyReflectConjecture_proved` (the Conjecture is now a theorem).
* **Consumed by.** `FiniteGeneralUniqueness.lean`.

### `GaussianWhoWhere/FiniteUniqueness.lean`
* **Role.** **Level 2** — concrete `P₁₆`-truncation finite uniqueness.
* **Definitions.** `Q4`, `Q4Poly`.
* **Theorems.** `Q4Poly_eq_one_of_translation`,
  `coeffs_zero_of_Q4Poly_eq_one`,
  `finite_concrete_uniqueness_P16_of_translation`,
  `finite_concrete_uniqueness_P16` (full multiplicativity form).
* **Consumed by.** None directly downstream (subsumed by §0
  `FiniteGeneralUniqueness`); kept for direct citation.

### `GaussianWhoWhere/FiniteGeneralUniqueness.lean`
* **Role.** **Level 2G** — arbitrary finite `K`-truncation finite
  uniqueness. The headline finite theorem.
* **Definitions.** `QFinitePoly K c`.
* **Theorems.** `coeff_P2nPoly_top`, `natDegree_P2nPoly`,
  `leadingCoeff_P2nPoly`,
  `QFinitePoly_eq_one_of_translation`,
  `coeffs_zero_of_QFinitePoly_eq_one` (descending induction on `K`),
  `finite_general_uniqueness_of_translation`,
  **`finite_general_uniqueness`** (full multiplicativity form,
  arbitrary `K`).
* **Consumed by.** Independent finite contribution.

### `GaussianWhoWhere/BridgeStructure.lean`
* **Role.** Type-level scaffold for the who/where bridge predicates.
* **Definitions.** `ReflectedZeroSymmetry`, `CriticalLineProperty`,
  `FunctionalSymmetry`, `ArithmeticIdentity`, `WhoWhereCompatible`.
* **Theorems.** `where_gives_reflected_zero_geometry`.
* **Consumed by.** `InfiniteCoupler.lean` (loosely; the predicates
  are the "outer" Bridge C type vocabulary).

---

## 1. Infinite Interface Layer

The original abstract Bridge C skeleton plus the L3 base (finite
exponential type, translation defect, sampled who-input, two-shift
coupler, top-level interface DAG).

### `GaussianWhoWhere/InfiniteCoupler.lean`
* **Role.** Abstract Bridge C coupler at the predicate level.
* **Definitions.** `HPftLike`, `InfiniteWho` (data-bearing),
  `InfiniteWhere`, `TwoTranslationExponentialRigidity`,
  `WhereKillsExponential`.
* **Theorems.** `infinite_who_where_rigidity` (composition of the
  two analytic inputs).
* **Consumed by.** Downstream Where files (`WhereKillsExponential`),
  the final pipeline.

### `GaussianWhoWhere/LogMultiplicativity.lean`
* **Role.** **Level 1 abstract core** + odd-log instantiation.
* **Definitions.** `oddLogSample`.
* **Theorems.**
  `polynomial_translation_identity_of_infinite_eval`,
  `polynomial_rigidity_of_infinite_sampled_translation`,
  `oddLogSample_injective`,
  `polynomial_rigidity_of_odd_log_sampled_translation`.
* **Consumed by.** `Infinite/LogSampleDensity.lean` and many
  downstream sampled-input files.

### `GaussianWhoWhere/Infinite/FiniteExponentialType.lean`
* **Role.** Definition and closure properties of `FiniteExpType`.
* **Definition.** `FiniteExpType F : Prop`.
* **Theorems.** `finiteExpType_const`, `finiteExpType_translate`,
  `finiteExpType_const_mul`, `finiteExpType_add`,
  `finiteExpType_sub`.
* **Consumed by.** `Infinite/TranslationDefect.lean`.

### `GaussianWhoWhere/Infinite/TranslationDefect.lean`
* **Role.** The defect `R_{a,A}(z) = Q(z + a) − A · Q(z)` and its
  finite-type closure.
* **Definitions.** `translationDefect`, `realLogShiftDefect`.
* **Theorems.** `finiteExpType_translationDefect`,
  `finiteExpType_realLogShiftDefect`.
* **Consumed by.** `Infinite/ZeroDensityInterface.lean`,
  `Infinite/TranslationDefectToEigenCoupler.lean`.

### `GaussianWhoWhere/Infinite/ZeroDensityInterface.lean`
* **Role.** Abstract `ZeroDensityForcesZero` predicate plus
  translation-defect ↔ global eigen relation.
* **Definitions.** `SampledZeros`, `ZeroDensityForcesZero`,
  `AbstractDenseEnough`.
* **Theorems.** `zeroDensity_forces_zero`,
  `translationDefect_eq_zero_of_sampledZeros`,
  `translation_eigen_of_translationDefect_eq_zero`,
  `translation_eigen_of_sampledZeros`.
* **Consumed by.** `Infinite/ArithmeticSamples.lean`,
  `Infinite/ZeroDensityForcesZeroRefined.lean`.

### `GaussianWhoWhere/Infinite/ArithmeticSamples.lean`
* **Role.** Single-shift sampled who-input.
* **Definitions.** `SampledTranslationRelation`, `SampledWhoInput`
  (`Type`-valued).
* **Theorems.**
  `sampledZeros_translationDefect_of_sampledTranslationRelation`,
  `translation_eigen_of_sampledTranslationRelation`,
  `SampledWhoInput.translation_eigen`.
* **Consumed by.** `Infinite/TwoShiftCoupler.lean`.

### `GaussianWhoWhere/Infinite/TwoShiftCoupler.lean`
* **Role.** Two-shift coupler — pair of `SampledWhoInput`s →
  global incommensurable eigen pair.
* **Definitions.** `TwoSampledWhoInputs`, `TwoGlobalTranslationEigen`,
  `TwoIncommensurableSampledWhoInputs`,
  `TwoIncommensurableGlobalTranslationEigen`.
* **Theorems.** `TwoSampledWhoInputs.translation_eigen₁ / ₂`,
  `TwoSampledWhoInputs.toGlobalTranslationEigen`,
  `TwoIncommensurableSampledWhoInputs.toGlobal`.
* **Consumed by.** `Infinite/ExponentialSurvivorInterface.lean`,
  `Infinite/SampledDefectToLogDerivConst.lean`.

### `GaussianWhoWhere/Infinite/ExponentialSurvivorInterface.lean`
* **Role.** Abstract reconstruction interface
  `incommensurable global pair ⇒ exp(c·z)`.
* **Definitions.** `ExponentialSurvivor`,
  `ExponentialSurvivorPrinciple`.
* **Theorems.**
  `exponential_survivor_of_two_global_translations`,
  `exponential_survivor_of_two_sampled_who_inputs`.
* **Consumed by.** `Infinite/WhereKillsExponential.lean`,
  `Infinite/InfiniteRigidity.lean`.

### `GaussianWhoWhere/Infinite/WhereKillsExponential.lean`
* **Role.** Pipeline applications combining the abstract
  `WhereKillsExponential` interface with `ExponentialSurvivor` to
  produce `Q ≡ 1`.
* **Theorems.** `one_of_where_and_exponential_survivor`,
  `infinite_who_where_rigidity_from_sampled_inputs`,
  `infinite_who_where_rigidity_from_global_translations`.
* **Consumed by.** `Infinite/InfiniteRigidity.lean`,
  `Infinite/GlobalLogDerivConstToExpInterface.lean`.

### `GaussianWhoWhere/Infinite/InfiniteRigidity.lean`
* **Role.** Top-level abstract DAG composition.
* **Theorems.**
  `infinite_rigidity_from_sampled_who_where`,
  `infinite_rigidity_from_global_who_where`,
  `bridgeC_infinite_coupler`.

---

## 2. Exponential Survivor / Log-Derivative Backbone

The chain that internalizes the analytic interfaces of §1 by working
with `complexLogDeriv Q := deriv Q / Q` and pushing real-axis
constancy / global constancy through the identity theorem.

### Chain

```
sampled defect (TranslationDefect, Defect→Eigen)
  → real translation eigen (TranslationEigenLogDerivInterface)
  → derivative eigen (TranslationEigenDeriv)
  → complexLogDeriv period (LogDerivativeAlgebra)
  → dense periods on ℝ (DensePeriodInterface, DensePeriodCoupler)
  → real-axis log-derivative constancy (LogDerivativeCoupler,
    ExponentialSurvivorConcrete, TwoIncommensurableSampledLogDerivConst,
    SampledDefectToLogDerivConst)
  → continuity supply (LogDerivativeContinuityInterface,
    LogDerivativeContinuityConcrete, LogDerivativeContinuityHolomorphic)
  → real-axis-to-global (RealAxisConstToGlobalInterface,
    RealAxisConstToGlobalConcrete, identity theorem witness)
  → reconstruction (GlobalLogDerivConstToExpInterface,
    GlobalLogDerivConstToExpNormalized, GlobalLogDerivConstToExpConcrete,
    via Mathlib's `logDeriv_eqOn_iff`)
```

### Files

* **`Infinite/TranslationZeros.lean`** — orbital zero propagation
  along eigen-direction (`zero_propagates_one_step` / `_nat` /
  `_backward_one_step` / `_int`).
* **`Infinite/DensePeriodInterface.lean`** — `IsPeriod`, `PeriodSet`,
  `DensePeriodSet`, algebraic period closure, the topological
  foothold `dense_periods_force_const_on_real`.
* **`Infinite/DensePeriodCoupler.lean`** — `IntegerPeriodSpan`,
  `two_periods_dense_span_force_const`,
  `two_incommensurable_periods_force_const`.
* **`Infinite/KroneckerDensity.lean`** — Mathlib bridge:
  `Irrational (a/b) ⇒ TwoIncommensurablePeriodsGenerateDense a b`.
* **`Infinite/KroneckerPipeline.lean`** — pipeline accepts
  `Irrational (a/b)` directly.
* **`Infinite/LogDerivativeCoupler.lean`** — `RealRestrict L`,
  `ComplexRealPeriod L a`, real-line restriction routing.
* **`Infinite/TranslationEigenLogDerivInterface.lean`** —
  `RealTranslationEigen Q a A`,
  `LogDerivRespectsRealTranslationEigen`.
* **`Infinite/LogDerivativeAlgebra.lean`** — `complexLogDeriv`,
  algebraic cancellation `Q'/Q` period from translation eigen +
  derivative eigen.
* **`Infinite/TranslationEigenDeriv.lean`** — chain-rule step
  (`deriv_eigen_of_realTranslationEigen`); the derivative-eigen
  hypothesis is internalized via Mathlib's `deriv_comp_add_const` +
  `deriv_const_mul_field`. Also `complexLogDeriv_eq_logDeriv` (bridge
  to Mathlib's `logDeriv`).
* **`Infinite/LogDerivativeContinuityInterface.lean`** —
  `LogDerivContinuousOnReal Q` predicate + final dispatcher.
* **`Infinite/LogDerivativeContinuityConcrete.lean`** — concrete
  witness from `Continuous Q + Continuous (deriv Q) + Q nonvanishing`.
* **`Infinite/LogDerivativeContinuityHolomorphic.lean`** — single
  hypothesis `Differentiable ℂ Q + Q nonvanishing` suffices.
* **`Infinite/SampledDefectToLogDerivConst.lean`** — sampled who
  input → real-axis log-deriv constancy in one step.
* **`Infinite/TwoIncommensurableSampledLogDerivConst.lean`** —
  variant for `TwoIncommensurableSampledWhoInputs`.
* **`Infinite/RealAxisConstToGlobalInterface.lean`** —
  `ConstantOnRealAxis`, `GloballyConstant`,
  `RealAxisConstExtendsGlobally`,
  `LogDerivRealAxisConstExtendsGlobally`.
* **`Infinite/RealAxisConstToGlobalConcrete.lean`** — identity-
  theorem witness via Mathlib's
  `AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure`.
* **`Infinite/ExponentialSurvivorConcrete.lean`** —
  `LogDerivHasComplexRealPeriod`,
  `LogDerivCandidate`, naming hooks tying the above into the
  reconstruction predicate.
* **`Infinite/TranslationDefectToEigenCoupler.lean`** —
  `realLogShiftDefect ≡ 0  ⇔  RealTranslationEigen` and the
  pipeline through it.
* **`Infinite/GlobalLogDerivConstToExpInterface.lean`** — full
  pipeline at interface level:
  `where_rigidity_of_twoIncomm_sampled_differentiable`.
* **`Infinite/GlobalLogDerivConstToExpNormalized.lean`** —
  reconstruction interface narrowed to `Q 0 = 1` form
  (`LogDerivEquationSolvesToExp`).
* **`Infinite/GlobalLogDerivConstToExpConcrete.lean`** —
  reconstruction *internalized* via `logDeriv_eqOn_iff` under
  `Differentiable ℂ Q + Q nonvanishing`.

---

## 3. Where Kills Exponential

The Where → exponent-zero reduction. Two layers: an exponent-level
algebraic core (no analytic content) and a function-level lift
(complex-exponential injectivity, internalized via derivatives).

### `Infinite/WhereKillsExponentialConcrete.lean`
* **Role.** Exponent-level algebraic core.
* **Definitions.** `ExponentReflection`, `ConcreteExponentialSurvivor`.
* **Theorems.** `exponentReflection_forces_zero`,
  `whereKillsExponentLevel`,
  `exponentReflection_of_linearExponentWhere`.

### `Infinite/WhereKillsExponentialFunctionLevel.lean`
* **Role.** Narrow Where lift interface.
* **Definitions.** `FunctionWhereForcesExponentReflection`.
* **Theorems.**
  `whereKillsExponential_of_functionWhereForcesExponentReflection`,
  `where_rigidity_of_twoIncomm_sampled_differentiable_irrational_exponentLift`.

### `Infinite/WhereKillsExponentialFunctionLevelConcrete.lean`
* **Role.** Function-level Where lift, **internalized** unconditionally.
  Differentiates `exp(c (1 − z)) = exp(c z)` at `z = 0` to extract
  `−c · exp c = c`, with `exp c = 1` from the value at `0`, hence
  `c = 0`.
* **Theorems.** `exp_linear_reflection_forces_zero` (private),
  `functionWhereForcesExponentReflection_concrete` (no extra
  hypothesis), **`where_rigidity_concrete_full`** (the C3 pipeline
  with the function-level Where lift removed from the input pack).

The headline of §3 is `where_rigidity_concrete_full`: it consumes
*concrete* hypotheses on `Q` plus the abstract
`ZeroDensityForcesZero` socket (which §4 then refines further).

---

## 4. Zero-Density Socket

The last analytic gap, sharpened into a single named socket
`JensenCartwrightLinearZeroBound`, plus all internalized
counting / specialization machinery around it.

### Files

* **`Infinite/ZeroCounting.lean`** — `RealLineZerosInInterval`,
  `HasAtMostLinearRealZeros` (the *shape* of a Jensen-style upper
  bound). Finite-witness style, no `Set.Finite` overhead.
* **`Infinite/ZeroDensityForcesZeroRefined.lean`** —
  `FiniteExpTypeLinearZeroBound` (in **nonzero** form: `F ≠ 0` is
  required, since the zero function fails the predicate),
  `LogSampleZeroContradictionReady`,
  `LogSampleZeroContradictionWithBound`,
  `zeroDensityForcesZero_of_logSampleContradictionReady_unbundled`,
  `zeroDensityForcesZero_of_logSampleContradictionWithBound`.
* **`Infinite/LogSampleDensity.lean`** — elementary log-sample
  combinatorics: `oddLogComplexSample`, monotonicity, an `N`-
  cardinality lower bound on the image at radius `log(2N + 1)`.
* **`Infinite/LogSampleZeroContradiction.lean`** — concrete
  density predicate `LinearZeroBoundBeatingLogSample u` (data-bearing)
  and the **counting collision**:
  `false_of_linearZeroBoundBeating_sampledZeros`,
  `logSampleZeroContradictionReady_of_linearZeroBoundBeating`,
  `zeroDensityForcesZero_of_linearZeroBoundBeating`.
* **`Infinite/OddLogLinearZeroBoundBeating.lean`** — concrete data
  witness for the odd-log sample, using
  `Real.isLittleO_log_id_atTop` to build a sample family beating
  any linear zero count: `eventually_linear_beats_log`,
  `oddLogLinearZeroBoundBeating`.
* **`Infinite/JensenCartwrightInterface.lean`** — the named socket
  `JensenCartwrightLinearZeroBound` (alias for the nonzero-form
  `FiniteExpTypeLinearZeroBound`),
  `zeroDensityForcesZero_oddLog_of_jensenCartwright`,
  `oddLogDenseEnough`,
  `zeroDensityForcesZero_for_oddLogSample`.
* **`Infinite/JensenFinalPipeline.lean`** — the **paper-level
  headline**
  **`where_rigidity_of_oddLogSample_from_jensenCartwright`**.
  Composes `JensenCartwrightLinearZeroBound` directly into
  `where_rigidity_concrete_full`.

### Decomposition

```
ZeroDensityForcesZero (linear-beating density predicate)
  ← FiniteExpTypeLinearZeroBound       — Jensen socket (left explicit)
  ← LogSampleZeroContradictionReady    — closed (counting collision)
  ← LinearZeroBoundBeatingLogSample    — closed at oddLogComplexSample
```

### Explicit non-claim

`JensenCartwrightLinearZeroBound` is **deliberately left as an
assumption**. The Lean development does not claim a proof of
Jensen / Cartwright zero counting, nor any RH-adjacent statement.
Every end-to-end theorem of §3 / §4 carries the socket
`JensenCartwrightLinearZeroBound` (or its synonym
`FiniteExpTypeLinearZeroBound`) explicitly in its hypothesis list.

---

## 5. ZetaBridge Branch

`Bridge C` is **already visible** in the architecture of zeta itself,
*before* any Hermite–Pochhammer formalization. The zeta branch is
recorded as a type-level scaffold; it does **not** connect to
`HP_ft` and does **not** claim RH.

### `GaussianWhoWhere/ZetaBridge/Basic.lean`
* **Role.** Type-level placeholders for the four architectural layers
  of the zeta object:

  * Who: Dirichlet series side (`BridgeA_DirichletLike`),
  * Who: Euler product side (`BridgeA_EulerProductLike`),
  * Bridge A′: logarithmic-derivative passage
    (`BridgeAprime_LogDerivLike`),
  * Where: completed functional equation (`CompletedWhereLike`).

* **Definitions.** `BridgeA_DirichletLike`,
  `BridgeA_EulerProductLike`, `BridgeAprime_LogDerivLike`,
  `CompletedWhereLike`, `ZetaBridgeCProfile`.
* **Theorems.** Four projection theorems from a profile to its
  layer.

* **Explicit non-claims.** No HP_ft connection, no RH claim. The
  zeta branch is interpretive; the HP branch is the formalization.

See `docs/BridgeCBranches.md` for the textual articulation of the
two branches.

---

## 6. Functional Equation Freezing

A short, independent algebraic theorem extracting the *local* form
of "Where freezes the real part of the first-order response" — a
freezing-operator interpretation of Where, valid abstractly without
any `HP_ft` content or any analytic socket.

### `GaussianWhoWhere/Infinite/FunctionalEquationFreezing.lean`
* **Definitions.** `IsRealComplex`, `IsPureImagComplex`.
* **Closure lemmas.** `realComplex_of_real`, `pureImag_mul_I`,
  `pureImag_neg`, `real_mul_pureImag`.
* **Main theorem.** `firstOrderResponse_pureImag_real`: if `D : ℂ`
  is purely imaginary and nonzero, then `−(eps · h)/D` is purely
  imaginary for every `eps, h : ℝ`.
* **Paper-facing.** `bridgeC_where_firstOrder_freezes_Re`
  (synonym `where_firstOrder_response_has_zero_real_part`) — under
  the algebraic Where condition, the real part of the first-order
  response is **frozen** to `0`.

---

## 7. Headline DAG Diagram

```
 ┌──────────────────────────────────────────────────────────────────┐
 │                        Finite Core (§0)                          │
 │                                                                  │
 │   PolynomialRigidity ─── HermitePochhammer ─── ConcretePolys     │
 │                              │                                   │
 │                              ▼                                   │
 │   FiniteUniqueness ─── FiniteGeneralUniqueness                   │
 │                              ▲                                   │
 │                  finite_general_uniqueness  (Headline finite)    │
 └──────────────────────────────────────────────────────────────────┘
                                   │
                                   │  conceptual recurrence
                                   ▼
 ┌──────────────────────────────────────────────────────────────────┐
 │                  Infinite C-HP Pipeline (§§1–4)                  │
 │                                                                  │
 │   FiniteExpType ─ TranslationDefect ─ ZeroDensityInterface       │
 │           │                                  │                   │
 │           │                                  ▼                   │
 │           │                          ArithmeticSamples           │
 │           │                                  │                   │
 │           │                                  ▼                   │
 │           │                          TwoShiftCoupler              │
 │           │                                  │                   │
 │           ▼                                  ▼                   │
 │   complexLogDeriv backbone ────────── ExponentialSurvivor*       │
 │           │                                  │                   │
 │           ▼                                  ▼                   │
 │   RealAxisConst → Global    ───────  GlobalLogDerivConstToExp*   │
 │   (identity theorem)                  (Mathlib logDeriv_eqOn_iff)│
 │           │                                  │                   │
 │           └──────────┬───────────────────────┘                   │
 │                      ▼                                           │
 │       where_rigidity_concrete_full   (§3)                        │
 │                      │                                           │
 │                      ▼                                           │
 │   JensenFinalPipeline:                                           │
 │     where_rigidity_of_oddLogSample_from_jensenCartwright         │
 │                      ▲                                           │
 │           ┌──────────┴──────────┐                                │
 │           │                     │                                │
 │     JensenCartwrightLinearZeroBound  ← only remaining socket    │
 │                      ▲                                           │
 │       (split internally:)                                        │
 │           ┌──────────┴──────────┐                                │
 │           │                     │                                │
 │    Jensen upper-bound        LogSampleZeroContradiction (§4)     │
 │      [LEFT EXPLICIT]              + OddLogLinearZeroBoundBeating │
 │                                       (closed)                   │
 └──────────────────────────────────────────────────────────────────┘

 ┌──────────────────────────────────────────────────────────────────┐
 │                    Branch C-zeta (§5)                            │
 │                                                                  │
 │   ZetaBridgeCProfile  —  type-level scaffold                     │
 │     Who = Dirichlet ⊕ Euler                                      │
 │     Bridge A′ = log derivative                                   │
 │     Where = completed functional equation                        │
 │                                                                  │
 │   No HP_ft connection. No RH claim.                              │
 └──────────────────────────────────────────────────────────────────┘

 ┌──────────────────────────────────────────────────────────────────┐
 │              Functional Equation Freezing (§6)                   │
 │                                                                  │
 │   bridgeC_where_firstOrder_freezes_Re                            │
 │     Where = first-order Re-freezing operator                     │
 │     (algebraic, no analytic socket, no HP_ft, no RH)             │
 └──────────────────────────────────────────────────────────────────┘
```

---

## 8. Status Summary

* **All implementation files are `sorry` / `admit`-free.**
  This is a project-wide invariant; no escape hatch is used in any
  Lean proof anywhere in `GaussianWhoWhere/`.

* **`JensenCartwrightLinearZeroBound` remains explicit by design.**
  It is the standard nonzero-finite-exponential-type linear-zero-
  counting theorem; no proof of it is attempted here, and no proof
  of any RH-adjacent statement is claimed.

* **No RH claim.** The Lean development *strictly* does not claim
  RH, the location of zeros of $\zeta$, or any equivalent.

* **What this contribution is.**
  1. The finite arbitrary-`K` Hermite–Pochhammer rigidity theorem
     `finite_general_uniqueness`, fully formalized.
  2. The Bridge C / `HP_ft` infinite pipeline, mechanically composed
     end-to-end down to a single classical analytic socket
     `JensenCartwrightLinearZeroBound`.
  3. A type-level scaffold for the zeta branch of Bridge C, recording
     the architectural recurrence without making analytic claims.
  4. A short freezing theorem
     `bridgeC_where_firstOrder_freezes_Re` formalizing the
     real-displacement core of Where as a stand-alone algebraic
     statement.

The Lean code base, the analytic-internalization roadmap, the
internal paper skeleton, the Bridge-C-branches document, and the
present DAG together provide a navigable, sorry-free formal map of
the program.
