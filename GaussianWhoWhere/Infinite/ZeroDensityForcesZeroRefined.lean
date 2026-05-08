import GaussianWhoWhere.Infinite.ZeroCounting
import GaussianWhoWhere.Infinite.ZeroDensityInterface

/-!
# Refined zero-density bridge (Infinite L3, Jensen socket part 2)

Decomposes the abstract `ZeroDensityForcesZero DenseEnough` interface
into two narrower sockets:

1. **Jensen-side upper bound.** For every `F : ℂ → ℂ` of finite
   exponential type, the real zeros of `F` satisfy a linear-growth
   counting bound (`HasAtMostLinearRealZeros F`).

2. **Sample-density-side contradiction.** Given that linear bound
   plus a sampled-zero hypothesis on a `DenseEnough` sample, the
   conclusion `F ≡ 0` follows.

Neither half is internalized at this layer; we only declare the
predicate shapes and route them into the original
`ZeroDensityForcesZero` interface. The Jensen / Cartwright bound
will populate (1); a counting-and-collision argument backed by
`Infinite/LogSampleDensity.lean` will populate (2).
-/

noncomputable section

namespace GaussianWhoWhere

/-- **Jensen-side upper-bound socket (nonzero form).** Asserts that
every *nonzero* finite-exponential-type function `F : ℂ → ℂ` satisfies
the linear zero-counting bound `HasAtMostLinearRealZeros F`. The
zero function is excluded explicitly: it has every real number as a
zero and so fails the predicate, but is also incompatible with the
sample-density-side hypotheses we will use it against, so excluding
it does not weaken the downstream conclusion.

The Jensen / Cartwright theorem is the canonical supplier of this
predicate. -/
def FiniteExpTypeLinearZeroBound : Prop :=
  ∀ {F : ℂ → ℂ},
    FiniteExpType F →
    F ≠ (fun _ : ℂ => 0) →
    HasAtMostLinearRealZeros F

/-- **Sample-density-side contradiction socket.** Given the linear
zero-counting bound (from Jensen) and the sampled-zero hypothesis on
a `DenseEnough` sample, conclude `F ≡ 0`.

Bundled-by-structure variant; alternatively the upstream user can
supply the upper-bound `hUpper` separately and use
`zeroDensityForcesZero_of_logSampleContradictionReady_unbundled`
below. -/
structure LogSampleZeroContradictionReady
    (DenseEnough : (ℕ → ℂ) → Prop) : Prop where
  force :
    ∀ {F : ℂ → ℂ} {u : ℕ → ℂ},
      FiniteExpType F →
      DenseEnough u →
      HasAtMostLinearRealZeros F →
      SampledZeros F u →
      F = fun _ : ℂ => 0

/-- **Refined zero-density principle, unbundled.** The Jensen-side
upper bound `hUpper` is taken as a separate hypothesis (in nonzero
form: `hUpper` only fires when `F ≠ 0`). -/
theorem zeroDensityForcesZero_of_logSampleContradictionReady_unbundled
    {DenseEnough : (ℕ → ℂ) → Prop}
    (h : LogSampleZeroContradictionReady DenseEnough)
    (hUpper : FiniteExpTypeLinearZeroBound) :
    ZeroDensityForcesZero DenseEnough := by
  refine ⟨?_⟩
  intro F u hF hu hzeros
  -- Either F is identically zero (done immediately), or apply the
  -- nonzero-form Jensen socket to obtain HasAtMostLinearRealZeros F
  -- and route into the contradiction-side rule.
  by_cases hFzero : F = (fun _ : ℂ => 0)
  · exact hFzero
  · exact h.force hF hu (hUpper hF hFzero) hzeros

/-- **Refined zero-density principle, bundled.** Variant where the
Jensen-side upper bound is bundled together with the contradiction
side into a single structure. -/
structure LogSampleZeroContradictionWithBound
    (DenseEnough : (ℕ → ℂ) → Prop) : Prop where
  upperBound : FiniteExpTypeLinearZeroBound
  ready : LogSampleZeroContradictionReady DenseEnough

/-- The bundled refined principle yields the abstract
`ZeroDensityForcesZero` interface. -/
theorem zeroDensityForcesZero_of_logSampleContradictionWithBound
    {DenseEnough : (ℕ → ℂ) → Prop}
    (h : LogSampleZeroContradictionWithBound DenseEnough) :
    ZeroDensityForcesZero DenseEnough :=
  zeroDensityForcesZero_of_logSampleContradictionReady_unbundled
    h.ready h.upperBound

end GaussianWhoWhere
