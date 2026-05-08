# Internal Paper Skeleton v0.1

## Working Title

**Who and Where in the Riemann Zeta Function:
Finite Hermite-Pochhammer Rigidity, Infinite Coupler Structure, and the Bridge C Program**

## Abstract Draft

We propose a structural decomposition of zeta-type rigidity into two
independent inputs: **Who**, corresponding to multiplicativity /
arithmetic identity, and **Where**, corresponding to functional symmetry
/ reflection geometry. Motivated by the Lean-level separation between
Euler-product identities and analytic zeta definitions, we introduce
the **Bridge C** viewpoint: zero geometry arises from a *coupler*
between arithmetic identity and analytic symmetry.

The finite part of the program is fully formalized in Lean. For
arbitrary finite Hermite-Pochhammer truncations

$$Q_K(x) = 1 + \sum_{k=1}^{K} c_k\, P_{4k}(x),$$

we prove that additive multiplicativity

$$Q_K(x+y) = Q_K(x)\, Q_K(y)$$

forces all coefficients $c_k = 0$. Thus, within every finite
Hermite-Pochhammer truncation, the Gaussian deformation factor is
uniquely selected.

The infinite extension is formalized at the **interface level**. We
isolate the analytic inputs required for the infinite Hermite-Pochhammer
class: finite exponential type, zero-density uniqueness, sampled
arithmetic translation, two-shift global translation eigen-relations,
exponential survivor, and Where-kills-exponential. These are assembled
in Lean into an abstract infinite rigidity theorem, while the analytic
components remain future internalization targets.

## 1. Introduction

### 1.1 Motivation: Doubting the Equality

Standard notation compresses several distinct layers into one line:

$$\zeta(s) = \sum_{n \geq 1} n^{-s} = \prod_p (1 - p^{-s})^{-1}.$$

However, in formal systems such as Lean / Mathlib, these are not simply
definitions of one object. They appear as typed bridges with explicit
hypotheses, especially $\operatorname{Re}(s) > 1$.

This suggests a structural reading:

* Euler product / Dirichlet series: arithmetic side.
* Analytic zeta / completed zeta: analytic side.
* RH: zero-geometry side.

The paper develops this separation into a formal Who/Where decomposition.

## 2. Lean-Induced Layer Separation

### 2.1 Euler Layer

The Euler layer consists of:

$$\sum n^{-s}, \qquad \prod_p (1 - p^{-s})^{-1},$$

together with complete multiplicativity, von Mangoldt data, and
prime-counting structures.

This layer answers: **Who is the arithmetic object?**

### 2.2 Riemann Layer

The analytic zeta object is defined through analytic continuation /
Hurwitz-zeta / theta-type constructions. It is *not* definitionally the
Euler product.

This layer carries:

* analytic continuation,
* completed zeta,
* functional equation,
* reflection symmetry.

It answers: **Where is the symmetry axis?**

### 2.3 RH / Zero Geometry Layer

The Riemann Hypothesis is not an Euler-product statement internally. It
is a statement about the zero geometry of the analytically continued
object:

$$\zeta(\rho) = 0 \implies \operatorname{Re}(\rho) = \tfrac{1}{2}.$$

## 3. Bridge A, Bridge B, Bridge C

### 3.1 Bridge A: Identity Bridge

Bridge A connects arithmetic expressions to the analytic zeta object in
the convergence half-plane:

$$\prod_p (1 - p^{-s})^{-1} = \zeta(s), \qquad \operatorname{Re}(s) > 1.$$

It is a **Who** bridge: it identifies the analytic function as the
arithmetic object.

### 3.2 Bridge A′: Log-Derivative Bridge

The logarithmic derivative bridge connects prime-power data to

$$-\frac{\zeta'(s)}{\zeta(s)}.$$

This passes through the transformation:

$$\prod \longrightarrow \sum \log \longrightarrow \frac{d}{ds} \log.$$

### 3.3 Bridge B: Explicit Formula Bridge

Bridge B returns zero geometry to arithmetic distribution:

$$\psi(x) = x - \sum_\rho \frac{x^\rho}{\rho} - \cdots.$$

It is the **zero-return** bridge.

### 3.4 Bridge C: Who-Where Coupler

The proposed Bridge C is not a single formula but a structural coupler:

$$\boxed{\text{Bridge C} = \mathcal{C}(\text{Who}, \text{Where})}$$

where:

* Who = multiplicativity / Euler identity,
* Where = functional equation / reflection symmetry.

The finite and infinite results below show that this is not merely
interpretive: the proof structure itself separates Who and Where.

## 4. Finite Hermite-Pochhammer Rigidity

### 4.1 Hermite-Pochhammer Deformations

Define polynomials $P_{2n}$ through the Hermite-Pochhammer construction.
In particular, for $k \geq 1$, the finite deformation family is:

$$Q_K(x) = 1 + \sum_{k=1}^{K} c_k\, P_{4k}(x).$$

The Lean project constructs:

* concrete $P_4, P_8, P_{12}, P_{16}$,
* general $P_{2n}$,
* recurrence,
* reflection law,
* finite Hermite-Pochhammer generation.

### 4.2 Finite Main Theorem

**Theorem — Finite Hermite-Pochhammer Rigidity.**

For every $K \in \mathbb{N}$, if

$$Q_K(x+y) = Q_K(x)\, Q_K(y) \quad \forall x, y \in \mathbb{R},$$

then

$$c_k = 0 \quad \forall k.$$

Equivalently, $Q_K \equiv 1$.

Lean theorem: `finite_general_uniqueness`.

### 4.3 Proof Idea

The proof has three layers:

1. **Polynomial translation rigidity.** If
   $Q(x + a) = Q(a)\, Q(x)$, $a \neq 0$, $Q(0) = 1$,
   then $Q = 1$.

2. **Degree and leading coefficient of $P_{2n}$.** The leading term of
   $P_{2n}$ is controlled by the highest Hermite-Pochhammer term, giving
   strictly increasing degrees for $P_{4k}$.

3. **Descending coefficient peeling.** In
   $Q_K = 1 + \sum c_k\, P_{4k}$, the highest-degree term involves only
   the last coefficient $c_K$. Thus $c_K = 0$, then descend.

### 4.4 Interpretation

In the finite polynomial setting, **Who alone is strong enough**:

$$\text{Who} \implies Q_K \equiv 1.$$

The finite polynomial nature kills the exponential survivor
automatically.

This is crucial because it contrasts with the infinite case.

## 5. Infinite Hermite-Pochhammer Program

### 5.1 Infinite Deformation

Consider

$$Q(z) = 1 + \sum_{k \geq 1} c_k\, P_{4k}(z).$$

Unlike the finite case, $Q$ is no longer a polynomial. It is an
entire-function candidate.

Thus the finite proof no longer applies directly.

### 5.2 $\mathrm{HP}_{\mathrm{ft}}$ Class

Define the intended analytic class:

$$\mathrm{HP}_{\mathrm{ft}} = \{\, Q(z) = 1 + \sum_{k \geq 1} c_k\, P_{4k}(z) : Q \text{ is entire of finite exponential type} \,\}.$$

Finite exponential type means roughly:

$$|Q(z)| \leq C\, e^{\tau\, |z|}.$$

In Lean, the growth component is represented by `FiniteExpType`, and
closure under constants, translation, scalar multiplication, addition,
and subtraction has been formalized.

### 5.3 Translation Defect

For $a, A \in \mathbb{C}$, define:

$$R_{a,A}(z) = Q(z + a) - A\, Q(z).$$

In the intended arithmetic application:

$$a = \log p, \qquad A = Q(\log p),$$

so:

$$R_p(z) = Q(z + \log p) - Q(\log p)\, Q(z).$$

Lean formalizes:

* `translationDefect`,
* `finiteExpType_translationDefect`.

Thus, if $Q$ is finite exponential type, so is $R_{a, A}$.

## 6. Infinite Coupler DAG

The infinite proof is decomposed into explicit interfaces.

### 6.1 Zero-Density Interface

Define:

* `SampledZeros`,
* `ZeroDensityForcesZero`.

This represents the analytic input:

$$R \in \mathrm{FiniteExpType},\ R(u_n) = 0 \text{ for sufficiently dense samples} \implies R \equiv 0.$$

This is not yet Jensen / Cartwright formalization. It is the *interface*
where that theorem will later attach.

### 6.2 Arithmetic Sampled Who Input

Define:

* `SampledTranslationRelation`,
* `SampledWhoInput`.

A sampled relation:

$$Q(u_n + a) = A\, Q(u_n)$$

implies:

$$R_{a,A}(u_n) = 0.$$

Together with zero-density uniqueness:

$$R_{a,A} \equiv 0.$$

Therefore:

$$Q(z + a) = A\, Q(z) \quad \forall z.$$

### 6.3 Two-Shift Coupler

Two sampled who inputs give two global translation eigen-relations:

$$Q(z + a_1) = A_1\, Q(z), \qquad Q(z + a_2) = A_2\, Q(z).$$

The intended arithmetic choices are:

$$a_1 = \log 2, \qquad a_2 = \log 3, \qquad \frac{\log 2}{\log 3} \notin \mathbb{Q}.$$

Lean formalizes the structure:

* `TwoSampledWhoInputs`,
* `TwoIncommensurableSampledWhoInputs`,
* `TwoGlobalTranslationEigen`,
* `TwoIncommensurableGlobalTranslationEigen`.

### 6.4 Exponential Survivor

The analytic principle is:

$$\text{two incommensurable global translations} \implies Q(z) = e^{c z}.$$

Lean currently represents this as:

* `ExponentialSurvivorPrinciple`,
* `ExponentialSurvivor`.

### 6.5 Where Kills the Survivor

The Where condition is:

$$Q(1 - z) = Q(z).$$

The exponential survivor gives:

$$Q(z) = e^{c z}.$$

Then Where forces:

$$c = 0,$$

so $Q \equiv 1$.

Lean packages this through:

* `InfiniteWhere`,
* `WhereKillsExponential`.

### 6.6 Infinite Rigidity Interface Theorem

The full Lean interface theorem is:

`infinite_rigidity_from_sampled_who_where`.

Conceptually:

$$\boxed{\,\text{FiniteExpType} + \text{ZeroDensity} + \text{Sampled Who} + \text{Exponential Survivor} + \text{Where} \implies Q \equiv 1\,}$$

This is the infinite Bridge C DAG.

### 6.7 Formal Lean Status: Infinite L3 Pipeline

Beyond the original interface DAG (Section 6.6), the project now
contains a sharpened end-to-end Lean theorem capturing the full C3
log-derivative backbone:

`where_rigidity_concrete_full`.

Schematically:

```
TwoIncommensurableSampledWhoInputs Q DenseEnough
  + ZeroDensityForcesZero DenseEnough
  + FiniteExpType Q
  + Differentiable ℂ Q
  + (∀ z, Q z ≠ 0)
  + real-shift identifications for the two sampled shifts
  + nonzero eigenvalues
  + InfiniteWhere Q
  + Irrational (a / b)
⇒ Q ≡ 1
```

**Status statement.** The full infinite Bridge C pipeline is now
mechanically composed in Lean, from sampled who-data and
differentiability / nonvanishing hypotheses all the way to
$Q \equiv 1$, with only one sharply localized analytic interface
remaining.

The remaining interface is:

1. **`ZeroDensityForcesZero DenseEnough`** —
   Jensen / Cartwright zero-density uniqueness on logarithmic samples
   (sample-density side partially internalized in
   `Infinite/LogSampleDensity.lean`; the analytic contradiction is
   not).

The formerly named analytic interfaces have been internalized:

* Kronecker density is supplied by `Irrational (a / b)` through
  `Infinite/KroneckerDensity.lean`;
* real-axis-to-global log-derivative continuation is supplied from
  analyticity of `complexLogDeriv Q` in
  `Infinite/RealAxisConstToGlobalConcrete.lean`;
* reconstruction from constant logarithmic derivative to exponential
  survivor is supplied by Mathlib's `logDeriv_eqOn_iff` in
  `Infinite/GlobalLogDerivConstToExpConcrete.lean`;
* the function-level Where lift is supplied by
  `Infinite/WhereKillsExponentialFunctionLevelConcrete.lean`.

**Project-wide invariants.**

* The **finite arbitrary-$K$ rigidity theorem**
  (`finite_general_uniqueness`) is `sorry`-free.
* The original **infinite interface DAG**
  (`infinite_rigidity_from_sampled_who_where`) is `sorry`-free.
* The **C3 log-derivative backbone**, from sampled two-shift data
  through `complexLogDeriv` real-axis constancy and onward to the
  $Q \equiv 1$ conclusion, is `sorry`-free.
* The **current project-wide invariant is no implementation proof
  placeholders**: every `.lean` file under `GaussianWhoWhere/`
  builds without `sorry`, `admit`, or any equivalent escape hatch.

This does **not** mean the analytic problem is solved at the Lean
level. It means the infinite C3 pipeline has been reduced to a single
file-located analytic wall: zero-density uniqueness for logarithmic
samples.

## 7. Finite vs Infinite: Why Bridge C Is Necessary

This is the conceptual core.

### 7.1 Finite Case

In finite polynomial truncations:

$$Q_K(x) = 1 + \sum_{k=1}^{K} c_k\, P_{4k}(x),$$

Who alone implies:

$$Q_K \equiv 1.$$

The polynomial constraint eliminates all nontrivial exponential
survivors.

Thus: **Finite: Who alone closes the system.**

### 7.2 Infinite Case

In the infinite entire-function setting, Who no longer forces $Q = 1$.
Instead, Who leads to:

$$Q(z) = e^{c z}.$$

Thus: **Infinite: Who leaves an exponential survivor.**

Only Where eliminates this survivor:

$$Q(1 - z) = Q(z) \implies c = 0.$$

Thus: **Infinite: Who + Where are both necessary.**

### 7.3 Bridge C Becomes Proof-Theoretic

Therefore Bridge C is not merely interpretation.

The finite/infinite contrast shows:

$$\boxed{\text{Who and Where are distinct proof inputs.}}$$

* Finite polynomiality hides the Where role.
* Infinite entire-function theory reveals it.

This is the strongest current formulation of the Who-Where Coupler.

## 8. Remaining Infinite Internalization Steps

The infinite DAG is currently *interface-formalized*. To turn it into a
full theorem, the following analytic interfaces must be internalized.

### Step I: Log Sample Density

Goal:

$$\#\{\, m : \log m \leq T,\ (m, p) = 1\,\} \sim C_p\, e^{T}.$$

Lean target: `LogSampleDensity.lean`.

Initial theorem can be weaker:

$$\#\{\, m \leq N : m \text{ odd}\,\} \geq c\, N.$$

Then translate to log samples via:

$$\log m \leq T \iff m \leq e^{T}.$$

### Step II: Zero-Density Uniqueness

Goal:

> If $F$ is nonzero entire of finite exponential type, then its
> zero-counting function cannot grow like $e^{T}$ on the real axis.

Needed concepts:

* zero counting,
* finite exponential type,
* Jensen formula or Cartwright class,
* density contradiction.

Lean targets:

* `ZeroCounting.lean`,
* `JensenInterface.lean`,
* `CartwrightInterface.lean`.

Practical first step: keep Jensen / Cartwright as interface, but
internalize the counting side.

### Step III: Two-Translation Exponential Survivor

Goal:

$$Q(z + a) = A\, Q(z), \quad Q(z + b) = B\, Q(z), \quad a/b \notin \mathbb{Q} \implies Q = e^{c z}.$$

Likely proof route:

* show $Q$ has no zeros,
* define $Q'/Q$,
* show $Q'/Q$ has two incommensurable periods,
* dense period group implies constant,
* integrate to get $Q = e^{c z}$.

Lean targets:

* `DensePeriods.lean`,
* `LogDerivative.lean`,
* `ExponentialSurvivor.lean`.

### Step IV: Where Kills Exponential

Goal:

$$e^{c z} = e^{c (1 - z)} \quad \forall z \implies c = 0.$$

This may be easier than the previous steps if formulated with a
normalization or derivative argument.

Lean target: `WhereKillsExponentialConcrete.lean`.

### Step V: $\mathrm{HP}_{\mathrm{ft}}$ Coefficient Conditions

Goal:

> Find coefficient decay assumptions on $c_k$ implying:

$$Q(z) = 1 + \sum c_k\, P_{4k}(z)$$

is entire of finite exponential type.

Possible route:

* Gelfand-Shilov-type coefficient decay,
* factorial bounds,
* Pochhammer growth estimates.

Lean target much later: `HPftCoefficientBounds.lean`.

## 9. Release Policy

### Current Status

* **Finite arbitrary $K$:** fully Lean-formalized.
* **Infinite coupler DAG:** Lean-formalized at interface level.
* **Infinite analytic inputs:** not yet internalized.

### Internal Release v0.1

Can be tagged now as:

`v0.1-finite-core-infinite-interface`

Meaning:

* finite theorem complete,
* infinite architecture complete,
* analytic interfaces isolated.

### Public Paper Release Criteria

Do not publicly release the full paper until at least one of:

* log sample density is internalized,
* where-kills-exponential is proved concretely,
* two-translation exponential survivor is partially internalized,
* zero-density uniqueness is substantially internalized.

The finite theorem alone may support a standalone finite-rigidity note,
but the Bridge C paper is stronger if at least one infinite analytic
interface is internalized.

## 10. Proposed Paper Structure

1. Introduction
2. Lean-Induced Layer Separation
3. Bridge A, Bridge B, and Bridge C
4. Hermite-Pochhammer Polynomials
5. Finite Arbitrary-$K$ Rigidity Theorem
6. Infinite $\mathrm{HP}_{\mathrm{ft}}$ Class
7. Infinite Coupler DAG
8. Finite vs Infinite: Why Where Becomes Necessary
9. Analytic Interfaces and Internalization Roadmap
10. Discussion: Bridge C Response Operators
11. Conclusion

## 11. Bridge C Response Operators

The next experimental direction remains:

$$\delta \rho_k = C_k[\delta Q].$$

Finite and infinite rigidity explain the *structural* constraints.
But the zero-specific response operators $C_k$ probe how individual
zeros react to breaking Who or Where.

This section connects back to the numerical Phase 1b result:

$$D_{\text{zero\_move}} \approx \tfrac{1}{6}\, D_{\text{logadd}}.$$

Future work:

* compute $C_k$ for more zeros,
* compare perturbation directions,
* separate Who-breaking and Where-breaking components,
* test whether $C_k$ has stable asymptotic behavior.

## 12. Current Internal Conclusion

* **Finite Hermite-Pochhammer rigidity is complete and formalized**
  (`finite_general_uniqueness`, `sorry`-free).
* **Infinite rigidity is decomposed into formal Lean interfaces, and
  the C3 log-derivative backbone is end-to-end composed in Lean**
  (`where_rigidity_of_twoIncomm_sampled_differentiable`,
  `sorry`-free, modulo five named analytic interfaces — see §6.7).
* **The finite/infinite contrast exposes Bridge C as a genuine
  Who-Where coupler.**
* **The remaining work is analytic internalization of those five
  named interfaces, not structural ambiguity.**
