import Mathlib
import GaussianWhoWhere.Infinite.OddLogLinearZeroBoundBeating

/-!
# Jensen / Cartwright interface (Infinite L3, the last analytic socket)

We do **not** prove Jensen / Cartwright in this file. Its purpose is
to fix a *named* socket for the final remaining analytic input of the
C3 pipeline,

  `JensenCartwrightLinearZeroBound`,

and connect it to the previously installed log-sample density
machinery so the abstract `ZeroDensityForcesZero` interface for the
concrete odd-log sample falls out as soon as the Jensen-side bound is
supplied.

The intended Jensen / Cartwright theorem reads, in standard form:

> If `F : ℂ → ℂ` is entire of finite exponential type and not
> identically zero, then the number of real zeros of `F` in `[0, R]`
> grows at most linearly in `R`.

This is exactly the predicate `FiniteExpTypeLinearZeroBound` from
`Infinite/ZeroDensityForcesZeroRefined.lean`; we re-package it here
under the more descriptive name so callers can plug in the eventual
Jensen / Cartwright proof through a single named adapter.
-/

noncomputable section

namespace GaussianWhoWhere

/-- **The Jensen / Cartwright socket.** A nonzero finite-exponential-
type function on `ℂ` has linear real-zero growth.

This is presently an alias for `FiniteExpTypeLinearZeroBound`; once
Jensen / Cartwright is internalized, the concrete proof slots in
here. -/
def JensenCartwrightLinearZeroBound : Prop :=
  FiniteExpTypeLinearZeroBound

/-- The Jensen-side socket yields the abstract zero-density principle
on the linear-beating density predicate (generic sample form). -/
theorem zeroDensityForcesZero_oddLog_of_jensenCartwright
    (hJC : JensenCartwrightLinearZeroBound) :
    ZeroDensityForcesZero
      (fun u : ℕ → ℂ => Nonempty (LinearZeroBoundBeatingLogSample u)) :=
  zeroDensityForcesZero_of_linearZeroBoundBeating hJC

/-- **Concrete witness.** The odd-log sample sequence
`oddLogComplexSample` satisfies the linear-beating density predicate.
This packages the `LinearZeroBoundBeatingLogSample` data witness
`oddLogLinearZeroBoundBeating` into the `Nonempty`-of form expected
by the density predicate. -/
theorem oddLogDenseEnough :
    Nonempty (LinearZeroBoundBeatingLogSample oddLogComplexSample) :=
  ⟨oddLogLinearZeroBoundBeating⟩

/-- **Final composition theorem (alias).** Identical conclusion to
`zeroDensityForcesZero_oddLog_of_jensenCartwright`; offered under a
more application-flavored name. -/
theorem zeroDensityForcesZero_for_oddLogSample
    (hJC : JensenCartwrightLinearZeroBound) :
    ZeroDensityForcesZero
      (fun u : ℕ → ℂ => Nonempty (LinearZeroBoundBeatingLogSample u)) :=
  zeroDensityForcesZero_oddLog_of_jensenCartwright hJC

end GaussianWhoWhere
