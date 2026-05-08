import Mathlib
import GaussianWhoWhere.Infinite.FiniteExponentialType

/-!
# Real-line zero counting (Infinite L3, Jensen socket part 1)

We do **not** prove Jensen / Cartwright here. The single content is
the *shape* of the zero-counting upper bound that Jensen-type theorems
will produce: a finite-witness style predicate stating that, for any
non-negative real radius `R`, the real zeros of `F` in `[0, R]` are
contained in some finite set whose cardinality grows at most linearly
in `R`.

This predicate provides the upper-bound side of the eventual
zero-density contradiction; the lower-bound side comes from
`Infinite/LogSampleDensity.lean`. The collision happens later in
`ZeroDensityForcesZeroRefined.lean`.

A note on the choice of formulation. We deliberately work with a
finite `Finset ℝ` containing all real zeros in `[0, R]`, rather than
`Set.toFinset` of the zero set, to avoid `Set.Finite` /
`Set.toFinset`-coercion overhead at this layer. The Jensen-side
provider can produce such a finite set (e.g. as the support of a
multiset of zeros counted with multiplicity).
-/

noncomputable section

namespace GaussianWhoWhere

/-- `RealLineZerosInInterval F R` records, for a non-negative radius
`R`, a finite set `S ⊆ ℝ` containing all zeros of `F` on the real
segment `[0, R]`. The accompanying `cardBound` field gives an upper
bound on `|S|` in terms of `R`. -/
structure RealLineZerosInInterval (F : ℂ → ℂ) (R : ℝ) where
  zeros : Finset ℝ
  contains_zeros :
    ∀ x : ℝ, 0 ≤ x → x ≤ R → F (x : ℂ) = 0 → x ∈ zeros

/-- **Linear zero-counting upper bound** (Jensen socket).

`HasAtMostLinearRealZeros F` asserts that there is a constant `C ≥ 0`
such that, for every non-negative `R`, the real zeros of `F` in
`[0, R]` are contained in a finite set of cardinality at most
`C · R + C`. (The additive `+ C` absorbs the small-`R` regime; it is
free in any standard Jensen / Cartwright bound.)

The intended supplier is a Jensen-type theorem applied to a function
`F` of finite exponential type. We do not prove that here; this file
only fixes the predicate shape. -/
def HasAtMostLinearRealZeros (F : ℂ → ℂ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℝ, 0 ≤ R →
      ∃ S : RealLineZerosInInterval F R,
        (S.zeros.card : ℝ) ≤ C * R + C

/-! ## Elementary closure remarks

We do not establish closure of `HasAtMostLinearRealZeros` under the
algebraic operations here; the eventual Jensen-side provider will
yield the predicate directly for the residue functions of interest.

The zero function `F ≡ 0` has every real number as a zero and so
**fails** `HasAtMostLinearRealZeros`: any finite witness set `S`
produced for radius `R = (S.card : ℝ) + 1` would need to contain
strictly more reals than `S.card` itself. This is the reason the
zero-density contradiction excludes `F = 0` separately. -/

end GaussianWhoWhere
