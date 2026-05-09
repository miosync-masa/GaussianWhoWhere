# Next Research Tasks

## Status

The previous implementation sprint is complete.  The current Lean
development has three stable pillars:

1. **C-HP:** the Hermite-Pochhammer infinite pipeline, ending in
   `where_rigidity_of_oddLogSample_from_jensenCartwright`, with one
   deliberately retained analytic socket:
   `JensenCartwrightLinearZeroBound`.
2. **C-zeta:** the zeta-architecture branch, in
   `GaussianWhoWhere/ZetaBridge/Basic.lean`, with the Dirichlet side
   of Bridge A now concretely backed by Mathlib.
3. **C-freezing:** the local first-order response theorem
   `bridgeC_where_firstOrder_freezes_Re`, formalizing the slogan
   "Where freezes real displacement."

This document replaces `docs/NextStepSprintPlan.md` as the active
planning document.  It does not prescribe immediate implementation.
It records the remaining semantic gaps and the possible directions for
closing or documenting them.

---

## 1. What `Set.EqOn F model domain` Means

The zeta-side interfaces now use the pattern:

```lean
∃ (domain : Set ℂ) (model : ℂ → ℂ),
  domain.Nonempty ∧ Set.EqOn F model domain
```

This is intentionally modest.  It says:

```text
On a specified nonempty domain, F agrees with a chosen model.
```

For example, the concrete Dirichlet-side bridge says:

```text
riemannZeta s = ∑' n, 1 / n^s
on the half-plane 1 < Re(s).
```

This is a real bridge, but it is not a whole analytic theory.

### 1.1 Included

`Set.EqOn F model domain` includes:

* a domain of comparison,
* a model function,
* equality of the analytic object with the model on that domain.

This is exactly what Bridge A-style statements usually provide:
an identity on a convergence region.

### 1.2 Not Included

`Set.EqOn F model domain` does **not** include:

* analytic continuation uniqueness,
* equality outside the stated domain,
* zero-location information,
* critical-line behavior,
* meromorphic continuation,
* residue data,
* pole structure,
* explicit formula machinery.

These omissions are deliberate.  The C-zeta branch is not an RH proof
and is not used to discharge the C-HP Jensen socket.

---

## 2. C-zeta Remaining Layers

The current C-zeta layer table is:

| Layer | Lean status | Meaning |
| --- | --- | --- |
| Bridge A, Dirichlet side | concrete Mathlib-backed | `riemannZeta = ∑ n^{-s}` on `1 < Re(s)` |
| Bridge A, Euler side | typed interface | Euler-product model still to connect |
| Bridge A′, log-derivative side | typed interface | logarithmic-derivative model still to connect |
| Where, completed reflection | concrete predicate shape | completed functional-equation layer |

## 2.1 Euler Product Side

Potential next Lean file:

```text
GaussianWhoWhere/ZetaBridge/EulerProduct.lean
```

Known Mathlib candidates include:

```lean
riemannZeta_eulerProduct_hasProd
riemannZeta_eulerProduct_tprod
riemannZeta_eulerProduct_exp_log
```

Possible goal:

```lean
theorem riemannZeta_bridgeA_eulerProduct :
    BridgeA_EulerProductLike riemannZeta := ...
```

This should still be framed as a Bridge A identity on the convergence
half-plane.  It should not claim anything about zeros or RH.

Open design question:

* Should `BridgeA_EulerProductLike` use a plain model `ℂ → ℂ`, or
  should it distinguish `HasProd`, `tprod`, and `exp (∑ log ...)`
  models?

The current `Set.EqOn` model is enough for a first wrapper, but the
Euler-product layer may deserve a more specific typed interface later.

## 2.2 Bridge A′ Log-Derivative Side

Potential next Lean file:

```text
GaussianWhoWhere/ZetaBridge/LogDerivative.lean
```

Semantic target:

```text
Euler product
  → logarithm
  → logarithmic derivative
  → prime-power / von Mangoldt type series
```

Possible interface:

```lean
BridgeAprime_LogDerivLike riemannZeta L
```

where `L` is a chosen logarithmic-derivative companion such as
`fun s => - deriv riemannZeta s / riemannZeta s`, with domain
excluding poles and zeros as needed.

Open design questions:

* Which domain is best?
  `1 < Re(s)` is safest for Euler-product differentiation.
* Should zeros / poles be excluded explicitly?
* Should the model be a von Mangoldt series, an Euler-log series, or
  a derivative of the Euler product?

This layer is conceptually important, but it is also where zeta zero
geometry begins to appear through poles of `-ζ'/ζ`.  Keep the scope
carefully bounded.

## 2.3 Completed Where Instance

Potential next Lean file:

```text
GaussianWhoWhere/ZetaBridge/Completed.lean
```

Known Mathlib candidate:

```lean
completedRiemannZeta_one_sub
```

Possible goal:

```lean
theorem completedRiemannZeta_completedWhereLike :
    CompletedWhereLike completedRiemannZeta :=
  completedRiemannZeta_one_sub
```

This would make the Where layer concrete for the zeta branch.

Boundary:

* This is a functional equation / reflection statement.
* It is not an RH statement.
* It does not assert zero locations.

---

## 3. Analytic Continuation and `EqOn`

A likely reviewer question:

> If `riemannZeta` agrees with a Dirichlet model on `1 < Re(s)`,
> why does this matter globally?

Current answer:

* In the zeta branch, it matters as a Bridge A identity.
* It does not, by itself, provide a global theorem.
* Global equality outside the domain would require analytic or
  meromorphic continuation machinery.

Possible future layer:

```text
GaussianWhoWhere/ZetaBridge/AnalyticContinuation.lean
```

Potential predicate:

```lean
structure AnalyticContinuationFromDomain
    (F model : ℂ → ℂ) (domain : Set ℂ) : Prop where
  eq_on_domain : Set.EqOn F model domain
  domain_accumulates : ...
  analytic_F : ...
  analytic_model : ...
  extends_to : ...
```

This should remain future work unless there is a clear local theorem
needed by the paper.  The current C-zeta claim does not need it.

---

## 4. Jensen / Cartwright Socket

The C-HP final theorem leaves one explicit classical socket:

```lean
JensenCartwrightLinearZeroBound
```

which is an alias for:

```lean
FiniteExpTypeLinearZeroBound
```

in canonical nonzero form:

```text
If F is a nonzero finite-exponential-type entire function,
then its real zeros in [0, R] admit an O(R) counting bound.
```

## 4.1 What Is Already Done

The Lean development has already internalized:

* the finite-witness real zero-counting predicate
  `HasAtMostLinearRealZeros`;
* the refined socket
  `FiniteExpTypeLinearZeroBound`;
* the generic counting collision
  `false_of_linearZeroBoundBeating_sampledZeros`;
* the odd-log sample witness
  `oddLogLinearZeroBoundBeating`;
* the final adapter
  `where_rigidity_of_oddLogSample_from_jensenCartwright`.

So the entire lower-bound / sample-density / pipeline side is closed.

## 4.2 What Remains

Only the classical upper-bound theorem remains:

```text
nonzero finite exponential type
  ⇒ linear real-zero counting upper bound
```

This is deliberately retained as a named assumption.  The project does
not claim a Lean proof of Jensen / Cartwright zero counting, and it
does not claim RH.

## 4.3 If One Ever Internalizes It

Potential future file:

```text
GaussianWhoWhere/Infinite/JensenCartwrightSupply.lean
```

Possible staged route:

1. define or reuse an "entire" predicate compatible with
   `FiniteExpType`;
2. prove isolated zeros for nonzero analytic functions;
3. obtain a finite zero set in compact disks or intervals;
4. import or prove a Jensen-style bound;
5. specialize the disk bound to real zeros in `[0, R]`;
6. package the result as `FiniteExpTypeLinearZeroBound`.

This is a classical-analysis project, not a Bridge C structural
project.  It should be treated as a known mountain, not as an
unresolved structural gap.

---

## 5. Functional Equation Freezing

The C-freezing theorem is complete at the algebraic first-order level:

```lean
bridgeC_where_firstOrder_freezes_Re
```

It proves:

```text
D purely imaginary and nonzero,
eps, h real
⇒ Re ( - eps*h / D ) = 0.
```

Interpretation:

```text
Where = first-order Re-freezing operator.
```

Potential future layers:

1. derive the real / purely-imaginary inputs from actual functional
   equation and conjugation symmetries;
2. connect to a simple-zero perturbation formula;
3. relate the denominator `D` to a stiffness source;
4. compare with numerical experiments.

These are optional extensions.  The algebraic core is already a Lean
theorem.

---

## 6. Recommended Next Actions

The old implementation sprint is complete.  The next work should be
chosen by paper needs, not by dependency pressure.

Reasonable options:

1. **Paper documentation.**
   Update `docs/InternalPaperSkeleton.md` with:
   * C-zeta Dirichlet side is Mathlib-backed,
   * C-freezing theorem statement,
   * Jensen socket intentionally retained.

2. **C-zeta Euler product wrapper.**
   Add `ZetaBridge/EulerProduct.lean` using existing Mathlib Euler
   product theorems.

3. **C-zeta completed Where wrapper.**
   Add `ZetaBridge/Completed.lean` wrapping
   `completedRiemannZeta_one_sub`.

4. **Freezing semantic extension.**
   Add the symmetry-to-real/pure-imaginary lemmas if needed for the
   paper.

5. **Jensen documentation only.**
   Leave `JensenCartwrightLinearZeroBound` as an explicit classical
   socket and do not attempt internalization.

---

## 7. Non-Claims

The current project does not claim:

* a Lean proof of RH,
* a Lean proof of Jensen / Cartwright zero-density theory,
* a derivation of HP_ft from zeta,
* a discharge of the HP-side Jensen socket using the zeta branch,
* zero-location control from `Set.EqOn` bridge predicates alone.

The contribution is the formal DAG, the finite theorem, the infinite
pipeline to a named classical socket, the zeta-architecture branch,
and the first-order freezing theorem.

