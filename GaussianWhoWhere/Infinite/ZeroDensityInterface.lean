import GaussianWhoWhere.Infinite.FiniteExponentialType
import GaussianWhoWhere.Infinite.TranslationDefect

/-!
# Zero-density interface (Infinite L3)

We do **not** prove Jensen / Cartwright / zero-counting here.
Instead we record the zero-density input as an abstract `Prop`-valued
interface:

  `R ∈ FiniteExpType, R(sample points) = 0  too often  ⇒  R ≡ 0`.

The "too often" predicate is left as a parameter `DenseEnough`; the
analytic content (a concrete density theorem about logarithmic
samples, etc.) is supplied later as an instance of
`ZeroDensityForcesZero`.

We then connect the interface to `translationDefect`: sampled zeros of
the defect give a global translation eigen-relation
`Q(z + a) = A · Q(z)`, which is the form required by the infinite
Bridge C analytic input.
-/

noncomputable section

namespace GaussianWhoWhere

/-- `SampledZeros F u` means that `F` vanishes on the sampled sequence
`u n` for every `n : ℕ`. In the intended application, `u n` is a
logarithmic sample such as `log m`, restricted to integers coprime to
a prime `p`. -/
def SampledZeros (F : ℂ → ℂ) (u : ℕ → ℂ) : Prop :=
  ∀ n : ℕ, F (u n) = 0

/-- Abstract zero-density uniqueness principle.

Interface for the analytic theorem

  *finite exponential type + too many sampled zeros ⇒ identically zero*.

The predicate `DenseEnough u` is intentionally abstract: a concrete
analytic density theorem will be supplied as an instance. -/
structure ZeroDensityForcesZero (DenseEnough : (ℕ → ℂ) → Prop) : Prop where
  force_zero :
    ∀ {F : ℂ → ℂ} {u : ℕ → ℂ},
      FiniteExpType F →
      DenseEnough u →
      SampledZeros F u →
      F = fun _ : ℂ => 0

/-- A minimal abstract density predicate, for interface-level
development. Carries no analytic content; it is a placeholder until a
concrete `DenseEnough` is plugged in. -/
def AbstractDenseEnough (_u : ℕ → ℂ) : Prop :=
  True

/-- Under a zero-density uniqueness principle, a finite-type function
with sampled zeros on a dense-enough sequence is identically zero. -/
theorem zeroDensity_forces_zero
    {DenseEnough : (ℕ → ℂ) → Prop}
    (hZD : ZeroDensityForcesZero DenseEnough)
    {F : ℂ → ℂ} {u : ℕ → ℂ}
    (hF : FiniteExpType F)
    (hu : DenseEnough u)
    (hzeros : SampledZeros F u) :
    F = fun _ : ℂ => 0 :=
  hZD.force_zero hF hu hzeros

/-! ## Connection with the translation defect -/

/-- If the translation defect `R_{a,A} = Q(· + a) − A · Q` vanishes on
a dense-enough sample, the zero-density principle forces it to be
identically zero. -/
theorem translationDefect_eq_zero_of_sampledZeros
    {DenseEnough : (ℕ → ℂ) → Prop}
    (hZD : ZeroDensityForcesZero DenseEnough)
    {Q : ℂ → ℂ} (hQ : FiniteExpType Q)
    (a A : ℂ) {u : ℕ → ℂ}
    (hu : DenseEnough u)
    (hzeros : SampledZeros (translationDefect Q a A) u) :
    translationDefect Q a A = fun _ : ℂ => 0 :=
  hZD.force_zero
    (finiteExpType_translationDefect hQ a A)
    hu
    hzeros

/-- Pointwise translation eigen-relation extracted from a vanishing
translation defect. -/
theorem translation_eigen_of_translationDefect_eq_zero
    {Q : ℂ → ℂ} {a A : ℂ}
    (hzero : translationDefect Q a A = fun _ : ℂ => 0) :
    ∀ z : ℂ, Q (z + a) = A * Q z := by
  intro z
  have hz := congrFun hzero z
  unfold translationDefect at hz
  exact sub_eq_zero.mp hz

/-- **Combined interface theorem.** Sampled zeros of the translation
defect (under a zero-density uniqueness principle and finite
exponential type of `Q`) yield the global translation eigen-relation

  `Q(z + a) = A · Q(z)`   for every `z : ℂ`,

i.e. exactly the input form consumed by the abstract Bridge C
coupler in `InfiniteCoupler.lean`. -/
theorem translation_eigen_of_sampledZeros
    {DenseEnough : (ℕ → ℂ) → Prop}
    (hZD : ZeroDensityForcesZero DenseEnough)
    {Q : ℂ → ℂ} (hQ : FiniteExpType Q)
    (a A : ℂ) {u : ℕ → ℂ}
    (hu : DenseEnough u)
    (hzeros : SampledZeros (translationDefect Q a A) u) :
    ∀ z : ℂ, Q (z + a) = A * Q z := by
  apply translation_eigen_of_translationDefect_eq_zero
  exact translationDefect_eq_zero_of_sampledZeros hZD hQ a A hu hzeros

end GaussianWhoWhere
