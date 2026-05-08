# Analytic Internalization Roadmap

## GaussianWhoWhere — Infinite Hermite-Pochhammer Program

**Status:** Internal roadmap
**Purpose:** Identify and sequence the analytic components needed to
upgrade the current infinite interface theorem into a fully
internalized Lean theorem.

---

## 0. Current State

The project currently has two completed formal components:

### Finite core

The arbitrary finite Hermite-Pochhammer truncation theorem is fully
formalized in Lean:

$$Q_K(x) = 1 + \sum_{k=1}^{K} c_k\, P_{4k}(x),$$

and

$$Q_K(x + y) = Q_K(x)\, Q_K(y) \quad \forall x, y$$

implies

$$c_k = 0 \quad \forall k.$$

Lean theorem:

```lean
finite_general_uniqueness
```

This part is complete and `sorry` / `admit` free.

### Infinite interface DAG and analytic backbone

The infinite Hermite-Pochhammer extension is currently formalized at
the interface level, with a substantial part of the two-shift
log-derivative backbone now internally composed.

The original top-level interface pipeline is:

```
FiniteExpType Q
  + sampled arithmetic who-inputs
  + zero-density uniqueness
  + two incommensurable translations
  + exponential survivor principle
  + where-kills-exponential principle
⇒ Q ≡ 1
```

Lean theorem:

```lean
infinite_rigidity_from_sampled_who_where
```

This theorem is also `sorry` / `admit` free, but several analytic
components are represented as explicit interfaces rather than
internally proved theorems.

In addition, the newer C3 pipeline now composes sampled two-shift data
all the way to final rigidity under named analytic bridge interfaces:

```
TwoIncommensurableSampledWhoInputs Q DenseEnough
  + ZeroDensityForcesZero DenseEnough
  + FiniteExpType Q
  + Differentiable ℂ Q
  + ∀ z, Q z ≠ 0
  + real-shift identifications for the two sampled shifts
  + nonzero eigenvalues
  + TwoIncommensurablePeriodsGenerateDense a b
  + LogDerivRealAxisConstExtendsGlobally Q
  + GlobalLogDerivConstForcesExponentialSurvivor Q
  + InfiniteWhere Q
  + WhereKillsExponential Q
⇒ Q ≡ 1
```

Lean theorem:

```lean
where_rigidity_of_twoIncomm_sampled_differentiable
```

This theorem has since been sharpened through a sequence of concrete
bridge replacements. The current headline theorem is:

```lean
where_rigidity_concrete_full
```

It keeps `ZeroDensityForcesZero DenseEnough` as the single remaining
abstract analytic input. The other formerly named analytic interfaces
have been internalized or replaced by concrete hypotheses:

* Kronecker density is supplied from `Irrational (a / b)`;
* real-axis constancy of `complexLogDeriv Q` is promoted globally from
  `AnalyticOnNhd ℂ (complexLogDeriv Q) Set.univ`;
* global constant log-derivative is reconstructed using Mathlib's
  `logDeriv_eqOn_iff`;
* the function-level Where lift is internalized in
  `WhereKillsExponentialFunctionLevelConcrete.lean`.

---

## 1. Goal

The long-term goal is to internalize enough analytic input to turn the
infinite interface theorem into a *genuine* theorem for an explicitly
defined analytic class:

$$\mathrm{HP}_{\mathrm{ft}} = \{\, Q(z) = 1 + \sum_{k \geq 1} c_k\, P_{4k}(z) : Q \text{ is entire of finite exponential type} \,\}.$$

Target theorem:

> If $Q \in \mathrm{HP}_{\mathrm{ft}}$, $Q(0) = 1$, $Q$ satisfies the
> arithmetic who-condition, and $Q$ satisfies the where-reflection
> condition, then $Q \equiv 1$.

Conceptually:

```
Who   ⇒ exponential survivor e^{cz}
Where ⇒ c = 0
Therefore Q ≡ 1
```

The finite case closes with **Who alone** because polynomiality kills
the exponential survivor.
The infinite case requires **both Who and Where**.

---

## 2. Analytic Interfaces Currently Isolated

The infinite DAG currently isolates the following analytic inputs.

### 2.1 Finite exponential type

**Current Lean status: partially internalized.**

Implemented:

* `FiniteExpType`,
* `finiteExpType_const`,
* `finiteExpType_translate`,
* `finiteExpType_const_mul`,
* `finiteExpType_add`,
* `finiteExpType_sub`,
* `finiteExpType_translationDefect`.

Meaning: if $Q$ is finite exponential type, then

$$R_{a,A}(z) = Q(z + a) - A\, Q(z)$$

is also finite exponential type.

This component is already internalized.

### 2.2 Zero-density uniqueness

**Current Lean status: interface only (sample-density side partially
internalized; see `Infinite/LogSampleDensity.lean`).**

Current interface: `ZeroDensityForcesZero`.

Sample-density-side internalization (the elementary, combinatorial
half) lives in `Infinite/LogSampleDensity.lean`:

* `oddLogComplexSample` (the `ℂ`-lift of the odd-log sample),
* `oddLogComplexSample_injective`,
* `oddLogSample_monotone`,
* `oddLogSample_le_of_index_lt`,
* `finite_many_odd_log_samples` (cardinality `N` after `N`-step image),
* `log_sample_linear_lower_bound_interface`
  (the concrete combinatorial input that the eventual zero-density
  contradiction will consume — at least `N` distinct samples in
  $(-\infty,\, \log(2N + 1)]$).

Intended analytic theorem:

> If $F$ is entire of finite exponential type and vanishes on a
> sufficiently dense logarithmic sample set, then $F \equiv 0$.

In the intended application:

$$F(z) = R_p(z) = Q(z + \log p) - Q(\log p)\, Q(z),$$

and

$$R_p(\log m) = 0 \quad ((m, p) = 1).$$

The sample set $\{\log m : (m, p) = 1\}$ has exponentially many points
in $[0, T]$:

$$\#\{\, m : \log m \leq T,\ (m, p) = 1\,\} \sim C_p\, e^{T}.$$

A nonzero entire function of finite exponential type should not have
that many real zeros.

### 2.3 Sampled arithmetic who-input

**Current Lean status: internalized abstractly.**

Implemented:

* `SampledTranslationRelation`,
* `SampledWhoInput`,
* `SampledZeros`,
* `translation_eigen_of_sampledTranslationRelation`,
* `TwoSampledWhoInputs`,
* `TwoIncommensurableSampledWhoInputs`.

Meaning: if sampled arithmetic relations provide

$$Q(u_n + a) = A\, Q(u_n),$$

then the translation defect vanishes on the sample:

$$R_{a,A}(u_n) = 0.$$

With zero-density uniqueness, this yields the global translation
relation:

$$Q(z + a) = A\, Q(z).$$

### 2.4 Two incommensurable translations imply exponential survivor

**Current Lean status: log-derivative backbone largely internalized;
three analytic bridges remain explicit interfaces.**

Current interface: `ExponentialSurvivorPrinciple`.

Intended analytic theorem:

> If $Q(z + a) = A\, Q(z)$, $Q(z + b) = B\, Q(z)$, with
> $a / b \notin \mathbb{Q}$, then $Q(z) = e^{c z}$ under appropriate
> analyticity / finite-type / nonvanishing assumptions.

Expected proof route:

1. Show $Q$ has no zeros.
2. Define logarithmic derivative $g(z) = Q'(z) / Q(z)$.
3. Show $g$ has periods $a$ and $b$.
4. Since $a / b \notin \mathbb{Q}$, the additive period group is dense
   on the real line.
5. Continuity / analyticity forces $g$ to be constant.
6. Integrate: $Q(z) = e^{c z}$.

Internalized pieces now include:

* `RealRestrict`, `ComplexRealPeriod`, and the real-axis coupler from
  complex-level real periods to `IsPeriod (RealRestrict L) a`;
* `IntegerPeriodSpan`, `two_periods_dense_span_force_const`, and
  `two_incommensurable_periods_force_const`;
* `RealTranslationEigen` and
  `LogDerivRespectsRealTranslationEigen`;
* `complexLogDeriv Q z = deriv Q z / Q z`;
* algebraic cancellation:
  translation eigen plus derivative eigen implies a period of
  `complexLogDeriv`;
* derivative eigen from translation eigen via Mathlib's derivative
  shift lemmas;
* `LogDerivContinuousOnReal` and concrete witnesses from
  `Continuous Q + Continuous (deriv Q) + Q` nonvanishing, and further
  from `Differentiable ℂ Q`;
* the bridge from `realLogShiftDefect Q t ≡ 0` to
  `RealTranslationEigen Q t (Q (t : ℂ))`;
* the sampled-input pipeline from `TwoSampledWhoInputs` and
  `TwoIncommensurableSampledWhoInputs` to real-axis constancy of
  `complexLogDeriv`;
* `ConstantOnRealAxis`, `GloballyConstant`, and the interface
  `LogDerivRealAxisConstExtendsGlobally`;
* the reconstruction interface
  `GlobalLogDerivConstForcesExponentialSurvivor`;
* the final sampled differentiable pipeline:
  `where_rigidity_of_twoIncomm_sampled_differentiable`.

Files:

* `Infinite/LogDerivativeCoupler.lean`
* `Infinite/ExponentialSurvivorConcrete.lean`
* `Infinite/TranslationEigenLogDerivInterface.lean`
* `Infinite/LogDerivativeAlgebra.lean`
* `Infinite/TranslationEigenDeriv.lean`
* `Infinite/LogDerivativeContinuityInterface.lean`
* `Infinite/TranslationDefectToEigenCoupler.lean`
* `Infinite/SampledDefectToLogDerivConst.lean`
* `Infinite/TwoIncommensurableSampledLogDerivConst.lean`
* `Infinite/LogDerivativeContinuityConcrete.lean`
* `Infinite/LogDerivativeContinuityHolomorphic.lean`
* `Infinite/RealAxisConstToGlobalInterface.lean`
* `Infinite/GlobalLogDerivConstToExpInterface.lean`

Internalized bridge replacements:

1. `TwoIncommensurablePeriodsGenerateDense a b` is supplied by
   `Irrational (a / b)` through `Infinite/KroneckerDensity.lean` and
   `Infinite/KroneckerPipeline.lean`.
2. `LogDerivRealAxisConstExtendsGlobally Q` is supplied from
   `AnalyticOnNhd ℂ (complexLogDeriv Q) Set.univ` in
   `Infinite/RealAxisConstToGlobalConcrete.lean`.
3. `GlobalLogDerivConstForcesExponentialSurvivor Q` is supplied from
   differentiability, nonvanishing, and normalization via
   `logDeriv_eqOn_iff` in
   `Infinite/GlobalLogDerivConstToExpConcrete.lean`.
4. `WhereKillsExponential Q` and
   `FunctionWhereForcesExponentReflection Q` are supplied by the
   concrete function-level Where lift in
   `Infinite/WhereKillsExponentialFunctionLevelConcrete.lean`.

The only remaining localized interface in the current headline theorem
is:

```lean
ZeroDensityForcesZero DenseEnough
```

This is the Jensen / Cartwright zero-density uniqueness wall.

### 2.5 Where kills exponential survivor

**Current Lean status: function-level lift internalized.**

Core files:

* `Infinite/WhereKillsExponentialConcrete.lean`,
* `Infinite/WhereKillsExponentialFunctionLevel.lean`,
* `Infinite/WhereKillsExponentialFunctionLevelConcrete.lean`.

Exponent-level core:

* `ExponentReflection c` (predicate `∀ z, c (1 − z) = c z`),
* `exponentReflection_forces_zero` (`ExponentReflection c ⇒ c = 0`),
* `ConcreteExponentialSurvivor Q c` (`Q = fun z => exp(c · z)`),
* `whereKillsExponentLevel` (the two together force `Q ≡ 1`).

Function-level lift:

* `functionWhereForcesExponentReflection_concrete`,
* `where_rigidity_concrete_full`.

The lift proves that if `Q z = exp(c * z)` and
`InfiniteWhere Q`, then `ExponentReflection c`.  It does this by
differentiating

```text
z ↦ exp(c * (1 - z)) = z ↦ exp(c * z)
```

at `z = 0`, using the value equality at `z = 0` to get `exp c = 1`,
and concluding `c = 0`.

Intended analytic theorem:

> If $Q(z) = e^{c z}$ and $Q(1 - z) = Q(z)$ for all $z$, then $c = 0$,
> and therefore $Q \equiv 1$.

This should be one of the easier analytic interfaces to internalize,
though complex exponential periodicity requires care.

### 2.6 $\mathrm{HP}_{\mathrm{ft}}$ coefficient realization

**Current Lean status: not yet internalized.**

Goal: relate Hermite-Pochhammer coefficient decay to finite exponential
type.

We want sufficient conditions on $c_k$ such that

$$Q(z) = 1 + \sum_{k \geq 1} c_k\, P_{4k}(z)$$

is entire of finite exponential type.

Possible directions:

* impose finite exponential type directly as part of $\mathrm{HP}_{\mathrm{ft}}$,
* derive finite type from strong coefficient decay,
* use Gelfand-Shilov style Hermite coefficient bounds,
* develop Pochhammer polynomial growth estimates.

---

## 3. Recommended Internalization Order

### Stage A — Completed

The following are done:

* **A1.** `FiniteExpType` definition
* **A2.** Closure under constants
* **A3.** Closure under translations
* **A4.** Closure under scalar multiplication
* **A5.** Closure under addition / subtraction
* **A6.** `TranslationDefect` finite-type closure
* **A7.** Sampled arithmetic who-input pipeline
* **A8.** Two-shift sampled-to-global interface
* **A9.** Exponential survivor interface
* **A10.** Where-kills-exponential interface
* **A11.** `InfiniteRigidity` top-level interface theorem

### Stage B — Low-risk next targets

These should be internalized before attacking Jensen / Cartwright.

#### B1. Concrete log-sample density, counting only

**Status: initial pass complete.** See
`GaussianWhoWhere/Infinite/LogSampleDensity.lean`.

Initial goals:

* Define simple sample sequences, e.g. $u_n = \log(2n + 1)$.
* Prove injectivity: $u_m = u_n \implies m = n$.
* Prove elementary counting lower bounds, e.g.
  $\#\{m \leq N : m \text{ odd}\} \geq N / 3$ or an equivalent simple
  bound.
* State or prove a bridge: $m \leq e^{T} \implies \log m \leq T$.

This stage does **not** prove zero-density uniqueness. It only
internalizes the sample-density side.

#### B2. Where kills exponential, normalized real-line version

**Status: exponent-level core complete.** See
`GaussianWhoWhere/Infinite/WhereKillsExponentialConcrete.lean`. The
algebraic step `ExponentReflection c ⇒ c = 0` and the resulting
`whereKillsExponentLevel` are no-sorry. The remaining gap is the
analytic lift from the function-level reflection
`Q(1 − z) = Q(z)` to the exponent-level reflection
`c (1 − z) = c z`, which requires complex-exponential injectivity
arguments not yet undertaken.

Avoid complex exponential periodicity at first.

Possible restricted theorem:

> If $Q(z) = e^{c z}$ and $Q(1 - z) = Q(z)$ for all real $z = t$, and
> $c \in \mathbb{R}$, then $c = 0$.

Or alternatively:

> If $\forall z,\ c (1 - z) = c z$, then $c = 0$.

This is weaker than the full complex exponential theorem but useful as
a foothold.

#### B3. Translation-eigen zero propagation

**Status: complete.** See
`GaussianWhoWhere/Infinite/TranslationZeros.lean`. Forward / `ℕ` /
backward / `ℤ` propagation along the eigen-direction is internalized,
with wrappers for both `trans₁` and `trans₂` of
`TwoGlobalTranslationEigen`.

Goal: if $Q(z + a) = A\, Q(z)$, then zeros propagate along the
$a$-orbit:

$$Q(z_0) = 0 \implies Q(z_0 + n a) = 0.$$

With two incommensurable shifts, this should lead toward dense-orbit
zero contradiction.

This is a component of the eventual exponential survivor theorem.

### Stage C — Medium-risk analytic structure

#### C1. Dense additive subgroup from two incommensurable real shifts

**Status: topological foothold and coupler complete; arithmetic side
still interface.** See
`GaussianWhoWhere/Infinite/DensePeriodInterface.lean` and
`GaussianWhoWhere/Infinite/DensePeriodCoupler.lean`.

The "topological half" is now internalized:

* `IsPeriod`, `PeriodSet`, `DensePeriodSet`,
* `period_zero`, `period_neg`, `period_add`,
* `integer_span_periods`
  (the integer ℤ-span of two periods is again a period),
* `dense_periods_force_const_on_real`
  (a continuous `ℝ → ℂ` whose period set is dense is constant — proved
  via `Continuous.ext_on` on the dense `PeriodSet`).

The arithmetic Kronecker-style theorem ("ℤ-span of two incommensurable
real shifts is dense") is left as the predicate
`TwoIncommensurablePeriodsGenerateDense`; concrete instances will be
supplied later (after a Mathlib search for an existing proof).

Possible future file: `GaussianWhoWhere/Infinite/KroneckerDensity.lean`.

Target theorem:

> If $a, b \in \mathbb{R}$ and $a / b \notin \mathbb{Q}$, then
> $\{m a + n b : m, n \in \mathbb{Z}\}$ is dense in $\mathbb{R}$.

This is a standard Kronecker-style theorem. **Check Mathlib first**;
do not reprove if available.

Potential use: if a continuous function has periods $a$ and $b$, with
$a / b \notin \mathbb{Q}$, then it is constant on horizontal real
lines.

#### C2. Periodic entire functions and dense periods

Create: `GaussianWhoWhere/Infinite/PeriodicEntire.lean`.

Target:

> If an entire function has two incommensurable real periods, then it
> is invariant under all real translations.

Additional assumptions may be needed to conclude it is constant.
If the function is also entire and invariant in one real direction, it
depends only on imaginary part; holomorphicity should force constancy.

This may be hard but decomposes cleanly.

#### C3. Logarithmic derivative interface refinement

**Status: backbone complete up to localized analytic bridge
interfaces.**

Implemented:

* `complexLogDeriv Q z = deriv Q z / Q z`;
* `RealTranslationEigen Q a A`;
* translation eigen implies derivative eigen for `deriv Q`;
* algebraic cancellation gives periods of `complexLogDeriv`;
* dense periods force `complexLogDeriv` to be constant on the real
  axis;
* `LogDerivContinuousOnReal` is supplied concretely by
  `Differentiable ℂ Q` plus nonvanishing;
* sampled who-inputs feed into the log-derivative constancy pipeline;
* real-axis constancy is packaged into `ConstantOnRealAxis`;
* global constancy and exponential reconstruction are isolated as
  explicit bridge interfaces.

Key endpoint theorems:

```lean
complexLogDeriv_const_on_real_of_twoIncomm_sampled_differentiable
globallyConstant_complexLogDeriv_of_twoIncomm_sampled_differentiable
exponentialSurvivor_of_twoIncomm_sampled_differentiable
where_rigidity_of_twoIncomm_sampled_differentiable
```

Remaining work in this stage:

* internalize `LogDerivRealAxisConstExtendsGlobally Q` using an
  identity theorem for analytic functions, applied to
  `complexLogDeriv Q`;
* internalize `GlobalLogDerivConstForcesExponentialSurvivor Q` by
  solving the differential equation $Q'/Q = c$, with normalization
  conditions as needed;
* combine the above with the concrete where-kills exponent-level
  result.

### Stage D — High-risk core theorem

#### D1. Zero-density uniqueness theorem

Create:

* `GaussianWhoWhere/Infinite/ZeroCounting.lean`,
* `GaussianWhoWhere/Infinite/JensenInterface.lean`,
* `GaussianWhoWhere/Infinite/CartwrightInterface.lean`.

Long-term target:

> If $F \not\equiv 0$ is entire of finite exponential type, then the
> number of zeros in a disk or interval has at most linear growth in
> radius, under suitable assumptions.

Then use sample density:

$$\#\{\log m \leq T\} \sim e^{T}$$

to force contradiction.

Possible intermediate theorem:

```lean
structure ZeroCountingBound (F : ℂ → ℂ) : Prop where
  bound :
    ∃ C : ℝ, ∀ R sufficiently large,
      zeroCount F R ≤ C * R
```

Then:

```
ZeroCountingBound F
  + ExponentialLogSampleZeros F
⇒ F ≡ 0
```

The Jensen / Cartwright theorem can remain an interface while the
contradiction from an explicit exponential lower bound is internalized.

### Stage E — $\mathrm{HP}_{\mathrm{ft}}$ coefficient realization

Create:

* `GaussianWhoWhere/Infinite/HPft.lean`,
* `GaussianWhoWhere/Infinite/HPftCoefficientBounds.lean`.

Define:

```lean
structure HPft (Q : ℂ → ℂ) : Prop where
  finiteType : FiniteExpType Q
  hermiteExpansion : ...
  reflectionCompatible : ...
```

At first, `hermiteExpansion` may remain an interface. Later, introduce
coefficient sequences $c_k$ and convergence assumptions.

Possible sufficient condition:

$$|c_k| \leq C\, A^{-k}\, (k!)^{-\alpha}$$

for sufficiently large $\alpha$.

The goal is **not** immediately full Schwartz generality. The first
target is a well-controlled finite-type Hermite-Pochhammer class.

---

## 4. Dependency Discipline

The infinite analytic files should import in this direction:

```
FiniteExponentialType
  ↓
TranslationDefect
  ↓
ZeroDensityInterface
  ↓
ArithmeticSamples
  ↓
TwoShiftCoupler
  ↓
ExponentialSurvivorInterface
  ↓
WhereKillsExponential
  ↓
InfiniteRigidity
```

Future internalization files should branch off without disturbing this
spine.

Suggested future import directions:

```
LogSampleDensity ───────→ ZeroDensityInterface
ZeroCounting / Jensen ──→ ZeroDensityInterface
DensePeriods ───────────→ ExponentialSurvivorInterface
LogDerivative ──────────→ ExponentialSurvivorInterface
WhereKillsConcrete ─────→ WhereKillsExponential
HPft ───────────────────→ InfiniteRigidity
```

Current C3 branch, already installed:

```
DensePeriodInterface
  ↓
DensePeriodCoupler
  ↓
LogDerivativeCoupler
  ↓
ExponentialSurvivorConcrete
  ↓
TranslationEigenLogDerivInterface
  ↓
LogDerivativeAlgebra
  ↓
TranslationEigenDeriv
  ↓
LogDerivativeContinuityInterface
  ↓
TranslationDefectToEigenCoupler
  ↓
SampledDefectToLogDerivConst
  ↓
TwoIncommensurableSampledLogDerivConst
  ↓
LogDerivativeContinuityConcrete
  ↓
LogDerivativeContinuityHolomorphic
  ↓
RealAxisConstToGlobalInterface
  ↓
GlobalLogDerivConstToExpInterface
```

**Do not make existing interface files depend on unfinished
analytic-heavy files.**

---

## 5. Release Criteria for Infinite Upgrade

### Internal v0.1

Already achieved:

```
finite arbitrary-K theorem
  + infinite interface DAG
```

### Internal v0.2

Target:

```
finite arbitrary-K theorem
  + infinite interface DAG
  + log sample density internalized
  + where-kills-exponential restricted theorem internalized
```

### Internal v0.3

Achieved in the C3 direction:

```
sampled two-shift input
  + differentiability / nonvanishing / finite type
  + zero-density interface
  + Kronecker interface
  + real-axis extension interface
  + reconstruction interface
  + where-kills interface
⇒ Q ≡ 1
```

Lean theorem:

```lean
where_rigidity_of_twoIncomm_sampled_differentiable
```

Separate D-stage target:

```
zero-counting contradiction internalized
  assuming Jensen / Cartwright bound interface
```

### Public preprint candidate

At least one of:

* zero-density uniqueness partially internalized,
* two-translation exponential survivor partially internalized
  (substantial C3 backbone now complete),
* where-kills-exponential fully internalized,
* $\mathrm{HP}_{\mathrm{ft}}$ coefficient class explicitly defined and
  nontrivial examples shown.

### Strong public version

Target:

```
finite arbitrary-K theorem
  + HP_ft class
  + zero-density theorem or sufficiently strong interface
  + exponential survivor theorem or sufficiently strong interface
  + where-kills-exponential theorem
```

---

## 6. Research Notes

### 6.1 Why finite does not need Where

In finite Hermite-Pochhammer truncations, $Q_K$ is a polynomial.

Who imposes a multiplicative Cauchy equation. The only analytic
survivor would be $e^{c z}$, but a polynomial cannot equal $e^{c z}$
unless $c = 0$.

Thus the finite theorem closes with **Who alone**.

### 6.2 Why infinite needs Where

In the infinite setting, $Q$ can be entire.

The Who condition is expected to leave:

$$Q(z) = e^{c z}.$$

This is *not* eliminated by entire finite-type structure alone.

The Where condition

$$Q(1 - z) = Q(z)$$

is what forces $c = 0$.

Thus the infinite case exposes the genuine two-input nature of
Bridge C.

### 6.3 Bridge C interpretation

Finite case:

```
Who + polynomiality ⇒ trivial Gaussian
```

Infinite case:

```
Who   ⇒ exponential survivor
Where ⇒ survivor killed
```

Therefore Bridge C is not just a philosophical label; it corresponds
to a structural split in the proof.

---

## 7. Immediate Next Implementation Candidates

The focused next-step sprint document is:

```text
docs/NextStepSprintPlan.md
```

Completed bridge replacements:

1. `Infinite/KroneckerDensity.lean` and
   `Infinite/KroneckerPipeline.lean`;
2. `Infinite/RealAxisConstToGlobalConcrete.lean`;
3. `Infinite/GlobalLogDerivConstToExpConcrete.lean`;
4. `Infinite/WhereKillsExponentialFunctionLevelConcrete.lean`;
5. `Infinite/ZeroCounting.lean`,
   `Infinite/ZeroDensityForcesZeroRefined.lean`, and
   `Infinite/LogSampleZeroContradiction.lean`
   (Jensen socket split plus the counting-collision side);
6. `Infinite/OddLogLinearZeroBoundBeating.lean`
   (concrete odd-log sample witness using
   `Real.isLittleO_log_id_atTop`).

Current recommended order:

1. `Infinite/JensenCartwrightInterface.lean`
   * isolate the exact analytic theorem that will supply
     `FiniteExpTypeLinearZeroBound`, now in its canonical nonzero form:
     `FiniteExpType F → F ≠ 0 → HasAtMostLinearRealZeros F`.
2. `Infinite/FunctionalEquationFreezing.lean`
   * formalize the first-order algebraic freezing lemma for the
     paper-side Bridge C interpretation.
3. `ZetaBridge/Basic.lean`
   * begin the separate zeta branch wrappers.

---

## 8. Current Guiding Principle

Do **not** try to prove the full infinite theorem in one step.

Instead:

```
interface → local theorem → internalized component → replace interface
```

Each interface should eventually become either:

* a theorem,
* a clearly named assumption,
* or a documented future target.

The finite theorem is complete.
The infinite theorem is now a dependency graph waiting to be
internalized.
