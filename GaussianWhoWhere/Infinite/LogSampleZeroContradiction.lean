import Mathlib
import GaussianWhoWhere.Infinite.ZeroDensityForcesZeroRefined
import GaussianWhoWhere.Infinite.LogSampleDensity

/-!
# Log-sample zero contradiction (Infinite L3, counting socket)

Closes the **contradiction-side** half of the refined zero-density
bridge from `Infinite/ZeroDensityForcesZeroRefined.lean`, *without*
touching Jensen / Cartwright.

The setup: we define a concrete `DenseEnough` predicate
`LinearZeroBoundBeatingLogSample u`, packaging — for the sample
sequence `u` — finite *families of points* in real intervals whose
cardinality strictly exceeds any prescribed linear upper bound
`C · R + C`. Such a sample is, by construction, strong enough to
contradict any `HasAtMostLinearRealZeros F` upper bound. Composing
with the Jensen-side socket
`FiniteExpTypeLinearZeroBound` then yields the abstract
`ZeroDensityForcesZero` interface for this concrete predicate.

The Jensen / Cartwright proof of `FiniteExpTypeLinearZeroBound` itself
is *not* attempted at this layer.
-/

noncomputable section

namespace GaussianWhoWhere

/-- **Concrete density predicate strong enough to beat every linear
zero-counting bound.** Records, for each `N : ℕ`, a finite family
`sampleSet N ⊆ ℝ` lying in `[0, radius N]`, all of whose elements lie
in the image of the sample sequence `u`, with the cardinality
strictly exceeding `C · radius N + C` for all sufficiently large `N`
(uniformly in any prescribed `C ≥ 0`).

The data fields (`sampleSet`, `radius`) prevent this from being a
`Prop`; we package it as a data-bearing structure analogous to
`InfiniteWho`. -/
structure LinearZeroBoundBeatingLogSample (u : ℕ → ℂ) where
  sampleSet : ℕ → Finset ℝ
  radius : ℕ → ℝ
  radius_nonneg : ∀ N : ℕ, 0 ≤ radius N
  card_gt :
    ∀ C : ℝ, 0 ≤ C →
      ∃ N : ℕ, C * radius N + C < ((sampleSet N).card : ℝ)
  in_interval :
    ∀ N : ℕ, ∀ x : ℝ, x ∈ sampleSet N → 0 ≤ x ∧ x ≤ radius N
  sampled :
    ∀ N : ℕ, ∀ x : ℝ, x ∈ sampleSet N → ∃ n : ℕ, u n = (x : ℂ)

/-- **Counting collision (False-form).** A
`LinearZeroBoundBeatingLogSample` sample combined with a linear
real-zero counting upper bound and a sampled-zero hypothesis is
inconsistent. This is the core algebraic / cardinality lemma; the
`F = 0` conclusion in the bridge below is then routed through
`by_cases` on whether `F` is identically zero. -/
theorem false_of_linearZeroBoundBeating_sampledZeros
    {F : ℂ → ℂ} {u : ℕ → ℂ}
    (hu : Nonempty (LinearZeroBoundBeatingLogSample u))
    (hUpper : HasAtMostLinearRealZeros F)
    (hzeros : SampledZeros F u) :
    False := by
  rcases hu with ⟨beat⟩
  rcases hUpper with ⟨C, hCnn, hbound⟩
  rcases beat.card_gt C hCnn with ⟨N, hcard⟩
  rcases hbound (beat.radius N) (beat.radius_nonneg N) with ⟨S, hScard⟩
  have hsubset : beat.sampleSet N ⊆ S.zeros := by
    intro x hx
    rcases beat.sampled N x hx with ⟨n, hun⟩
    have hFx : F (x : ℂ) = 0 := by
      rw [← hun]
      exact hzeros n
    rcases beat.in_interval N x hx with ⟨hx0, hxR⟩
    exact S.contains_zeros x hx0 hxR hFx
  have hcard_le : (beat.sampleSet N).card ≤ S.zeros.card :=
    Finset.card_le_card hsubset
  have hcard_le_real : ((beat.sampleSet N).card : ℝ) ≤ (S.zeros.card : ℝ) := by
    exact_mod_cast hcard_le
  have hbad : ((beat.sampleSet N).card : ℝ) ≤ C * beat.radius N + C :=
    le_trans hcard_le_real hScard
  exact absurd hbad (not_le.mpr hcard)

/-- **Generic counting collision.** A `LinearZeroBoundBeatingLogSample`
sample beats every linear zero-counting upper bound, hence (combined
with the upper bound itself) forces `F = 0`. -/
theorem logSampleZeroContradictionReady_of_linearZeroBoundBeating :
    LogSampleZeroContradictionReady
      (fun u : ℕ → ℂ => Nonempty (LinearZeroBoundBeatingLogSample u)) := by
  refine ⟨?_⟩
  intro F u _hF hu hUpper hzeros
  exact (false_of_linearZeroBoundBeating_sampledZeros hu hUpper hzeros).elim

/-- **Refined zero-density principle, concrete bundle for the
linear-beating predicate.** Combines the Jensen-side socket
`hUpper : FiniteExpTypeLinearZeroBound` with the counting collision
`logSampleZeroContradictionReady_of_linearZeroBoundBeating`. -/
theorem zeroDensityForcesZero_of_linearZeroBoundBeating
    (hUpper : FiniteExpTypeLinearZeroBound) :
    ZeroDensityForcesZero
      (fun u : ℕ → ℂ => Nonempty (LinearZeroBoundBeatingLogSample u)) :=
  zeroDensityForcesZero_of_logSampleContradictionReady_unbundled
    logSampleZeroContradictionReady_of_linearZeroBoundBeating
    hUpper

end GaussianWhoWhere
