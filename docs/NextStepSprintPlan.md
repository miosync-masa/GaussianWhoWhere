# Next Step Sprint Plan

## Purpose

This document records the next implementation sequence after the
current Infinite L3 pipeline.

The current headline theorem is:

```lean
where_rigidity_concrete_full
```

At this point the bridge replacements from the previous sprint have
closed:

1. function-level where-to-exponent lift,
2. real-axis-to-global log-derivative continuation,
3. reconstruction from constant log-derivative to exponential survivor,
4. Kronecker density from `Irrational (a / b)`.

The remaining abstract analytic input in the headline theorem is:

```lean
ZeroDensityForcesZero DenseEnough
```

The next work should split into three logically separate tracks:

```text
Sprint 1: Zero-density wall
Sprint 2: FreezingLemma
Sprint 3: ZetaBridge
Sprint 4: Bridge C branch separation
```

The guiding rule is:

```text
Do not mix HP deformation rigidity with the concrete zeta bridge.
```

The HP branch studies deformation factors `Q`.
The zeta branch studies Mathlib's concrete zeta objects.
The freezing branch extracts the algebraic content of Where as a
real-part-freezing operator.

---

## Sprint 0 — Closed: Current Infinite L3 Bridge Interfaces

### 0.1 Function-Level Where Exponent Lift

Target file:

```text
GaussianWhoWhere/Infinite/WhereKillsExponentialFunctionLevelConcrete.lean
```

Goal:

Turn the existing function-level lift interface into a concrete theorem.

Existing pieces:

```lean
ExponentReflection
exponentReflection_forces_zero
whereKillsExponentLevel
FunctionWhereForcesExponentReflection
WhereKillsExponential
```

Target theorem shape:

```lean
theorem functionWhereForcesExponentReflection_of_exponential_form
    {Q : ℂ → ℂ} :
    FunctionWhereForcesExponentReflection Q := by
  ...
```

Mathematical core:

If

```text
Q z = Complex.exp (c * z)
Q (1 - z) = Q z
```

for all `z`, then

```text
Complex.exp (c * (1 - z)) = Complex.exp (c * z)
```

for all `z`.  This should force `c = 0`; then
`ExponentReflection c` follows.

Recommended proof routes:

1. Differentiate the function equality
   `fun z => exp (c * (1 - z)) = fun z => exp (c * z)`.
   At `z = 0`, this gives `-c * exp c = c`.  Combine with the value
   equality at `z = 0` / `z = 1` if needed.
2. Alternatively, choose a special `z` so the exponent difference is
   `1`, and contradict `Complex.exp_eq_one_iff`.

Expected wrapper:

```lean
theorem whereKillsExponential_of_functionWhereForcesExponentReflection
    {Q : ℂ → ℂ}
    (hlift : FunctionWhereForcesExponentReflection Q) :
    WhereKillsExponential Q
```

If this wrapper already exists, just add the concrete lift theorem and
a final pipeline theorem replacing `hlift`.

Verification:

```bash
lake env lean GaussianWhoWhere/Infinite/WhereKillsExponentialFunctionLevelConcrete.lean
grep -nE "\bsorry\b|\badmit\b" GaussianWhoWhere/Infinite/WhereKillsExponentialFunctionLevelConcrete.lean
```

### 0.2 Analytic Witness for `complexLogDeriv Q`

Target file:

```text
GaussianWhoWhere/Infinite/LogDerivativeAnalyticConcrete.lean
```

Goal:

Supply the concrete hypothesis

```lean
AnalyticOnNhd ℂ (complexLogDeriv Q) Set.univ
```

from analyticity and nonvanishing of `Q`.

Target theorem shape:

```lean
theorem analyticOnNhd_complexLogDeriv_of_analyticOnNhd_nonvanishing
    {Q : ℂ → ℂ}
    (hQ : AnalyticOnNhd ℂ Q Set.univ)
    (hQnz : ∀ z : ℂ, Q z ≠ 0) :
    AnalyticOnNhd ℂ (complexLogDeriv Q) Set.univ := by
  ...
```

Likely proof:

```lean
unfold complexLogDeriv
exact hDeriv.div hQ (by intro z hz; exact hQnz z)
```

where `hDeriv` is obtained from `hQ` using Mathlib's analytic
derivative API.  If `hQ.deriv` is available, use it directly.  If not,
derive it through:

```lean
have hQdiffOn : DifferentiableOn ℂ Q Set.univ := hQ.differentiableOn
have hDerivDiffOn : DifferentiableOn ℂ (deriv Q) Set.univ :=
  hQdiffOn.deriv isOpen_univ
have hDeriv : AnalyticOnNhd ℂ (deriv Q) Set.univ :=
  hDerivDiffOn.analyticOnNhd isOpen_univ
```

Then add a final theorem replacing the explicit analytic-log-derivative
hypothesis in the current strongest pipeline.

Verification:

```bash
lake env lean GaussianWhoWhere/Infinite/LogDerivativeAnalyticConcrete.lean
grep -nE "\bsorry\b|\badmit\b" GaussianWhoWhere/Infinite/LogDerivativeAnalyticConcrete.lean
```

---

## Sprint 1 — Zero-Density Wall

### Aim

Refine the last remaining interface:

```lean
ZeroDensityForcesZero DenseEnough
```

Do not attempt the full Jensen / Cartwright proof first.  The first
step is to make the zero-counting and sample-density contradiction
interfaces match the already-internalized `LogSampleDensity.lean`.

Target files:

```text
GaussianWhoWhere/Infinite/ZeroCounting.lean
GaussianWhoWhere/Infinite/ZeroDensityForcesZeroRefined.lean
GaussianWhoWhere/Infinite/LogSampleZeroContradiction.lean
```

Status: the three files above are complete.  They split the original
`ZeroDensityForcesZero` interface into:

```text
FiniteExpTypeLinearZeroBound
  -- Jensen / Cartwright analytic upper-bound socket

LinearZeroBoundBeatingLogSample
  -- sample-side lower-bound predicate

LogSampleZeroContradictionReady
  -- generic counting collision
```

The generic theorem now available is:

```lean
zeroDensityForcesZero_of_linearZeroBoundBeating
```

The socket has been refined to the canonical nonzero form:

```lean
def FiniteExpTypeLinearZeroBound : Prop :=
  ∀ {F : ℂ → ℂ},
    FiniteExpType F →
    F ≠ (fun _ : ℂ => 0) →
    HasAtMostLinearRealZeros F
```

### 1.1 Zero Counting Predicates

Create `ZeroCounting.lean`.

Suggested definitions:

```lean
def RealLineZerosInInterval (F : ℂ → ℂ) (R : ℝ) : Set ℝ :=
  {x : ℝ | 0 ≤ x ∧ x ≤ R ∧ F (x : ℂ) = 0}

def HasAtMostLinearRealZeros (F : ℂ → ℂ) : Prop :=
  ∃ C R₀ : ℝ, 0 ≤ C ∧ 0 ≤ R₀ ∧
    ∀ R : ℝ, R₀ ≤ R →
      (RealLineZerosInInterval F R).Finite ∧
      ((RealLineZerosInInterval F R).toFinset.card : ℝ) ≤ C * R
```

If `Set.toFinset` is awkward, use a finite witness:

```lean
def HasAtMostLinearRealZeros (F : ℂ → ℂ) : Prop :=
  ∃ C R₀ : ℝ, 0 ≤ C ∧ 0 ≤ R₀ ∧
    ∀ R : ℝ, R₀ ≤ R →
      ∃ S : Finset ℝ,
        (∀ x : ℝ, 0 ≤ x → x ≤ R → F (x : ℂ) = 0 → x ∈ S) ∧
        (S.card : ℝ) ≤ C * R
```

Prefer the finite-witness version if it makes proofs lighter.

### 1.2 Dense Log Sample Contradiction Shape

Create `ZeroDensityForcesZeroRefined.lean`.

Goal:

Define a refined predicate that says a sample sequence supplies too many
distinct real zeros for any nonzero finite-type function with a linear
zero-counting bound.

Suggested structure:

```lean
structure LogSampleZeroContradictionReady
    (DenseEnough : (ℕ → ℂ) → Prop) : Prop where
  force :
    ∀ {F : ℂ → ℂ} {u : ℕ → ℂ},
      DenseEnough u →
      FiniteExpType F →
      HasAtMostLinearRealZeros F →
      (∀ n : ℕ, F (u n) = 0) →
      F = fun _ : ℂ => 0
```

Then add a bridge:

```lean
theorem zeroDensityForcesZero_of_logSampleContradictionReady
    {DenseEnough : (ℕ → ℂ) → Prop}
    (h : LogSampleZeroContradictionReady DenseEnough) :
    ZeroDensityForcesZero DenseEnough := by
  ...
```

The bridge may need to match the exact fields in
`ZeroDensityInterface.lean`; read that file first and adapt the theorem
signature accordingly.

### 1.3 Jensen / Cartwright Interface

Create `JensenCartwrightInterface.lean`.

Do not prove Jensen yet.  Isolate the exact theorem needed:

```lean
def JensenCartwrightLinearZeroBound : Prop :=
  ∀ F : ℂ → ℂ,
    Entire F →
    FiniteExpType F →
    F ≠ fun _ : ℂ => 0 →
    HasAtMostLinearRealZeros F
```

If the project does not yet have `Entire`, use the existing analytic
predicate style:

```lean
AnalyticOnNhd ℂ F Set.univ
```

instead of introducing a new notion.

### 1.4 Deliverable

This sprint is successful when the project has a no-placeholder
composition theorem of the form:

```lean
JensenCartwrightLinearZeroBound
  → LogSampleZeroContradictionReady DenseEnough
  → ZeroDensityForcesZero DenseEnough
```

or a close equivalent matching existing field names.

Verification:

```bash
lake env lean GaussianWhoWhere/Infinite/ZeroCounting.lean
lake env lean GaussianWhoWhere/Infinite/ZeroDensityForcesZeroRefined.lean
lake env lean GaussianWhoWhere/Infinite/LogSampleZeroContradiction.lean
```

### 1.5 Odd-Log Specialization

Target file:

```text
GaussianWhoWhere/Infinite/OddLogLinearZeroBoundBeating.lean
```

Status: complete.

Goal:

Specialize the generic counting predicate to the existing odd-log
sample:

```lean
theorem oddLogLinearZeroBoundBeating :
    LinearZeroBoundBeatingLogSample oddLogComplexSample := by
  ...
```

Use:

```lean
sampleSet N := (Finset.range N).image oddLogSample
radius N := Real.log (((2 * N + 1 : ℕ) : ℝ))
```

Already available:

```lean
finite_many_odd_log_samples
log_sample_linear_lower_bound_interface
oddLogComplexSample_injective
```

Main remaining growth lemma:

```lean
theorem eventually_linear_beats_log
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ N : ℕ,
      C * Real.log (((2 * N + 1 : ℕ) : ℝ)) + C < N := by
  ...
```

Status: complete, using Mathlib's
`Real.isLittleO_log_id_atTop`.

Recommended proof route:

Use asymptotic / filter facts rather than elementary inequalities.
Search Mathlib first:

```bash
rg -n "tendsto.*log|log.*tendsto|isLittleO.*log|log.*isLittleO|log_div|div_atTop" \
  .lake/packages/mathlib/Mathlib | head -80
```

Likely target:

```text
(fun N : ℕ => Real.log ((2 * N + 1 : ℝ)) / (N : ℝ)) → 0
```

Then obtain eventually

```text
C * log(2N+1) + C < N
```

The concrete witness now available is:

```lean
oddLogLinearZeroBoundBeating
```

### 1.6 Remaining Jensen Socket

At this point the sample side is fully internalized for
`oddLogComplexSample`.  The remaining analytic socket is exactly:

```lean
FiniteExpTypeLinearZeroBound
```

Equivalently:

```text
nonzero finite exponential type function
  ⇒ O(R) real-zero counting bound
```

Next target file:

```text
GaussianWhoWhere/Infinite/JensenCartwrightInterface.lean
```

First pass goal:

Do not attempt the full Jensen proof.  Define the named analytic
provider and connect it to the final pipeline:

```lean
def JensenCartwrightLinearZeroBound : Prop :=
  FiniteExpTypeLinearZeroBound

theorem zeroDensityForcesZero_oddLog_of_jensenCartwright
    (hJC : JensenCartwrightLinearZeroBound) :
    ZeroDensityForcesZero
      (fun u : ℕ → ℂ =>
        Nonempty (LinearZeroBoundBeatingLogSample u)) :=
  zeroDensityForcesZero_of_linearZeroBoundBeating hJC
```

If desired, add a more explicitly analytic variant:

```lean
def AnalyticFiniteExpTypeLinearZeroBound : Prop :=
  ∀ {F : ℂ → ℂ},
    AnalyticOnNhd ℂ F Set.univ →
    FiniteExpType F →
    F ≠ (fun _ : ℂ => 0) →
    HasAtMostLinearRealZeros F
```

Then prove the implication to `FiniteExpTypeLinearZeroBound` only if
the project's `FiniteExpType` already implies analyticity elsewhere.
Otherwise keep it as a separate future socket.

---

## Sprint 2 — FreezingLemma

### Aim

Formalize the first-order algebraic core:

```text
Where symmetry freezes the real part of a simple-zero response.
```

Target file:

```text
GaussianWhoWhere/Infinite/FunctionalEquationFreezing.lean
```

### 2.1 Basic Predicates

Define:

```lean
def IsRealComplex (z : ℂ) : Prop := z.im = 0
def IsPureImagComplex (z : ℂ) : Prop := z.re = 0
```

or use existing Mathlib predicates if convenient.  Prefer the simplest
definitions that make `simp [Complex.ext_iff]` and `ring_nf` effective.

### 2.2 Algebraic Freezing Core

Target theorem:

```lean
theorem firstOrderResponse_pureImag
    {eps h D : ℂ}
    (heps : IsRealComplex eps)
    (hh : IsRealComplex h)
    (hD : IsPureImagComplex D)
    (hDnz : D ≠ 0) :
    IsPureImagComplex (-(eps * h) / D) := by
  ...
```

Equivalent real-parameter version:

```lean
theorem firstOrderResponse_pureImag_real
    {eps h : ℝ} {D : ℂ}
    (hD : IsPureImagComplex D)
    (hDnz : D ≠ 0) :
    IsPureImagComplex (-((eps : ℂ) * (h : ℂ)) / D) := by
  ...
```

This is the safest first target.  The proof is just complex arithmetic:
write `D = I * y` or use real / imaginary parts and `field_simp`.

### 2.3 Real-Part Freezing

Target theorem:

```lean
theorem bridgeC_where_firstOrder_freezes_Re
    {eps h D : ℂ}
    (heps : IsRealComplex eps)
    (hh : IsRealComplex h)
    (hD : IsPureImagComplex D)
    (hDnz : D ≠ 0) :
    ((-(eps * h) / D).re = 0) := by
  exact firstOrderResponse_pureImag heps hh hD hDnz
```

If `IsPureImagComplex` is defined as `z.re = 0`, this is immediate.

### 2.4 Symmetry Supplies Real / Pure Imaginary

Second layer, after the algebraic core is clean:

```lean
theorem where_symmetric_value_real_on_critical_line
    {H : ℂ → ℂ} {γ : ℝ}
    (hreflect : ∀ z, H (1 - z) = H z)
    (hconj : ∀ z, H (star z) = star (H z)) :
    IsRealComplex (H ((1 / 2 : ℝ) + γ * Complex.I)) := by
  ...
```

Derivative version:

```lean
theorem reflected_derivative_pureImag_on_critical_line
    ...
```

Do not start with the derivative version unless the algebraic theorem is
already complete.

### 2.5 Deliverable

The first pass is successful once these two theorems are clean:

```lean
firstOrderResponse_pureImag_real
bridgeC_where_firstOrder_freezes_Re
```

This gives the paper-side phrase:

```text
The first-order algebraic content of Where as a real-part-freezing
operator is formalized.
```

---

## Sprint 3 — ZetaBridge

### Aim

Create a zeta-side bridge layer that wraps Mathlib zeta facts in
Bridge C vocabulary.

This sprint must not claim that zeta is an HP deformation factor.
It only records that Mathlib's zeta-side objects provide concrete
instances of Bridge A, Bridge A-prime, and Where-style structure.

Target file:

```text
GaussianWhoWhere/ZetaBridge/Basic.lean
```

Optional later files:

```text
GaussianWhoWhere/ZetaBridge/Dirichlet.lean
GaussianWhoWhere/ZetaBridge/EulerProduct.lean
GaussianWhoWhere/ZetaBridge/LogDerivative.lean
GaussianWhoWhere/ZetaBridge/Completed.lean
```

### 1.1 Namespace and Lightweight Predicates

Create:

```lean
namespace GaussianWhoWhere
namespace ZetaBridge
```

Define lightweight predicates first, even before importing every zeta
theorem:

```lean
def BridgeA_DirichletLike (F : ℂ → ℂ) : Prop := ...
def BridgeA_EulerProductLike (F : ℂ → ℂ) : Prop := ...
def BridgeAprime_LogDerivLike (F L : ℂ → ℂ) : Prop := ...
def CompletedWhereLike (Λ : ℂ → ℂ) : Prop :=
  ∀ s : ℂ, Λ (1 - s) = Λ s
```

Keep these definitions simple.  They are labels for the paper-level
bridge decomposition, not the final analytic theorem.

### 1.2 Concrete Wrappers Around Mathlib

Search first:

```bash
rg -n "riemannZeta|RiemannZeta|zeta|completed|EulerProduct|logDeriv|vonMangoldt" \
  $(pwd)/.lake/packages/mathlib/Mathlib | head -80
```

Expected wrapper names:

```lean
zeta_bridgeA_dirichlet
zeta_bridgeA_eulerProduct
zeta_bridgeAprime_logDeriv
zeta_where_completed
```

If a Mathlib theorem has difficult hypotheses, wrap it as a theorem
whose assumptions exactly mirror Mathlib.  Do not weaken or redesign
the theorem in this sprint.

### 1.3 Deliverable

At the end of Sprint 1, there should be a zeta namespace with named
Bridge wrappers, even if some are still very thin aliases of Mathlib
facts.

Expected import update:

```lean
import GaussianWhoWhere.ZetaBridge.Basic
```

in `GaussianWhoWhere.lean` only after the file is clean.

---

## Sprint 4 — Bridge C Branch Separation

### Aim

Make the HP branch and zeta branch visibly separate in docs and Lean
namespaces.

Deliverable docs:

```text
docs/BridgeCBranches.md
```

Suggested structure:

```text
Bridge C
  Branch C-HP
    object: deformation factor Q
    who: spectral sampled translation / multiplicativity
    where: Q(1-z)=Q(z)
    wall: Jensen / Cartwright zero-density

  Branch C-zeta
    object: zeta / completed zeta / log derivative
    who: Euler product / Dirichlet series
    where: completed functional equation
    wall: meromorphic continuation / residue / explicit formula
```

Lean namespace targets:

```lean
namespace GaussianWhoWhere.HPBridge
namespace GaussianWhoWhere.ZetaBridge
```

This sprint is mostly architectural.  Do not move working files unless
the import churn is small.  Prefer adding aliases and documentation
over refactoring the active theorem DAG.

Verification:

```bash
lake env lean GaussianWhoWhere.lean
```

Run the full umbrella only if imports were touched.  Otherwise use
single-file checks.

---

## Recommended Order

```text
1.  refined zero-density wall
2.  Freezing algebra core
3.  ZetaBridge wrappers
4.  Bridge C branch separation doc
```

If only one next file is chosen, choose:

```text
GaussianWhoWhere/Infinite/ZeroCounting.lean
```

Reason: the current final theorem has exactly one remaining abstract
analytic input, and zero counting is the smallest entrance to that
wall.
