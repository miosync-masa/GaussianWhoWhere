import Mathlib
import GaussianWhoWhere.LogMultiplicativity

/-!
# Log-sample density (Infinite L3, low-risk)

Internalizes only the **elementary** log-sample side of the
zero-density interface. We do **not** define zero counting, prove any
Jensen / Cartwright bound, or work with `exp(T)` asymptotics at this
stage; those belong to later layers.

The single concrete content here is:

* a `ℂ`-valued lift `oddLogComplexSample n := (oddLogSample n : ℂ)`,
* monotonicity and pointwise upper bound of `oddLogSample`,
* a counting statement: there are at least `N` distinct odd-log
  samples in `[0, log(2N + 1)]`.

The last theorem (`log_sample_linear_lower_bound_interface`) is a
concrete combinatorial statement, intentionally weaker than an
exponential lower bound; it provides the input that the eventual
zero-density theorem will consume.
-/

noncomputable section

namespace GaussianWhoWhere

/-! ## Complex lift -/

/-- The odd-log sample sequence lifted to `ℂ`. -/
def oddLogComplexSample (n : ℕ) : ℂ :=
  (oddLogSample n : ℂ)

theorem oddLogComplexSample_injective :
    Function.Injective oddLogComplexSample := by
  intro m n h
  have hreal : oddLogSample m = oddLogSample n := by
    have hcoe : ((oddLogSample m : ℂ) : ℂ) = ((oddLogSample n : ℂ) : ℂ) := h
    exact_mod_cast hcoe
  exact oddLogSample_injective hreal

/-! ## Real-side combinatorial properties -/

/-- For `n < N`, the underlying odd integer satisfies
`2*n + 1 ≤ 2*N + 1`. -/
theorem odd_index_value_bound {n N : ℕ} (h : n < N) :
    2 * n + 1 ≤ 2 * N + 1 := by
  omega

/-- `oddLogSample` is monotone: `m ≤ n ⇒ oddLogSample m ≤ oddLogSample n`. -/
theorem oddLogSample_monotone : Monotone oddLogSample := by
  intro m n hmn
  unfold oddLogSample
  have hm : (0 : ℝ) < ((2 * m + 1 : ℕ) : ℝ) := by positivity
  have hcast : ((2 * m + 1 : ℕ) : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 2 * m + 1 ≤ 2 * n + 1)
  exact Real.log_le_log hm hcast

/-- For every `n < N`, `oddLogSample n ≤ log(2*N + 1)`. -/
theorem oddLogSample_le_of_index_lt {n N : ℕ} (h : n < N) :
    oddLogSample n ≤ Real.log (((2 * N + 1 : ℕ) : ℝ)) := by
  unfold oddLogSample
  have hpos : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by positivity
  have hcast : ((2 * n + 1 : ℕ) : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) := by
    exact_mod_cast odd_index_value_bound h
  exact Real.log_le_log hpos hcast

/-! ## Counting statement -/

/-- The image of `Finset.range N` under `oddLogSample` has cardinality
`N`. (Equivalently: the first `N` odd-log samples are pairwise
distinct.) -/
theorem finite_many_odd_log_samples (N : ℕ) :
    ((Finset.range N).image oddLogSample).card = N := by
  rw [Finset.card_image_of_injective _ oddLogSample_injective]
  exact Finset.card_range N

/-- **Concrete linear-style lower bound.** There are at least `N`
distinct odd-log samples in `(-∞, log(2*N + 1)]`. Formally: the image
of `Finset.range N` under `oddLogSample` has cardinality `N`, and every
element of that image lies in the interval `(-∞, log(2*N + 1)]`.

This is the elementary input the zero-density layer will eventually
consume; it is intentionally a finite combinatorial statement, not an
`exp(T)`-style asymptotic. -/
theorem log_sample_linear_lower_bound_interface (N : ℕ) :
    ((Finset.range N).image oddLogSample).card = N
      ∧ ∀ x ∈ (Finset.range N).image oddLogSample,
          x ≤ Real.log (((2 * N + 1 : ℕ) : ℝ)) := by
  refine ⟨finite_many_odd_log_samples N, ?_⟩
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨n, hn, rfl⟩
  exact oddLogSample_le_of_index_lt (Finset.mem_range.mp hn)

end GaussianWhoWhere
