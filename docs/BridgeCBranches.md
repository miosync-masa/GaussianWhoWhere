# Bridge C Branches

## Principle

Bridge C splits into two branches.

The Hermite–Pochhammer branch (`C-HP`) is the formalization target the
Lean development has been pursuing: a who/where coupler on a finite
or finite-exponential-type deformation factor `Q`. The zeta branch
(`C-zeta`) is the *interpretive observation* that the same who/where
architecture is already present in the standard analytic structure of
the Riemann zeta function — Bridge C is not invented from `HP_ft`; it
is recurrent in the architecture of $\zeta$ itself.

This document records the split, fixes the analytic layers and the
remaining sockets, and is intentionally non-prescriptive about the
zeta branch beyond its existence.

## Branch C-HP

**Object.** Hermite–Pochhammer deformation factor `Q : ℂ → ℂ` (finite
truncation `Q_K(x) = 1 + Σ c_k · P_{4k}(x)` or
finite-exponential-type infinite analogue).

**Who.** Sampled / spectral translation multiplicativity, packaged
as `TwoIncommensurableSampledWhoInputs Q DenseEnough` plus the
real-shift identifications and nonzero eigenvalues.

**Where.** `Q(1 − z) = Q(z)` (`InfiniteWhere Q`).

**Status.** The Lean pipeline is complete up to one named classical
analytic socket:

* `JensenCartwrightLinearZeroBound` — a nonzero finite-exponential-
  type function on `ℂ` has linear real-zero growth.

The headline theorem is

```
where_rigidity_of_oddLogSample_from_jensenCartwright
  : JensenCartwrightLinearZeroBound
  → (concrete C3 hypotheses on Q)
  → (TwoIncommensurableSampledWhoInputs at log 2 / log 3-style shifts)
  → Q ≡ 1.
```

Every other former analytic interface (Kronecker arithmetic density,
real-axis-to-global analytic continuation, log-derivative
reconstruction, the function-level Where lift) has been internalized
in Lean and replaced by concrete predicates.

## Branch C-zeta

**Object.** $\zeta$, the completed $\Lambda$, and the logarithmic
derivative $-\zeta'/\zeta$.

**Who.** Two compatible identity layers:

* the Dirichlet series side $\sum n^{-s}$,
* the Euler product side $\prod_p (1 - p^{-s})^{-1}$.

**Bridge A′.** The logarithmic derivative layer: a passage from the
Euler product to a sum over prime powers via $\prod \to \sum \log
\to (d/ds)\log$.

**Where.** The completed functional equation
$\Lambda(1 - s) = \Lambda(s)$.

**Purpose.** This branch *explains* why Bridge C arises naturally
from the zeta architecture. It is **not** an `HP_ft` theorem and
**does not** claim RH. The four layers of `C-zeta` are recorded at
the type level in
[`GaussianWhoWhere/ZetaBridge/Basic.lean`](../GaussianWhoWhere/ZetaBridge/Basic.lean)
as content-free placeholders; concrete identifications and analytic
relations are deferred to a later development.

## Note on the boundary

Branches `C-HP` and `C-zeta` are deliberately decoupled in the Lean
development. In particular:

* The zeta branch is **not** used to discharge any analytic socket on
  the Hermite–Pochhammer side. `JensenCartwrightLinearZeroBound`
  remains an explicit hypothesis (or an explicit assumption) in every
  end-to-end theorem of `C-HP`.
* The zeta branch makes **no claim about RH** at any layer.
* No theorem in the zeta branch consumes Hermite–Pochhammer data, and
  no theorem in the Hermite–Pochhammer branch consumes zeta data.

The two branches share only the named architectural pattern
(who/where coupler with a Bridge A′ logarithmic-derivative passage).
That pattern is the substantive observation of this document.
