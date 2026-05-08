import GaussianWhoWhere.Infinite.FiniteExponentialType

/-!
# Translation defect — finite exponential type closure (Infinite L3)

Defines the **translation defect**

  `R_{a,A}(z) := Q(z + a) − A · Q(z)`,

intended for the infinite Hermite–Pochhammer extension at the choice
`a = log p`, `A = Q(log p)`, where it becomes

  `R_p(z) = Q(z + log p) − Q(log p) · Q(z)`.

The single result of this file is that the finite-exponential-type
class is closed under forming this defect, by direct composition of
the translate / const-mul / sub closure lemmas from
`FiniteExponentialType.lean`.

A real-shift specialization `realLogShiftDefect` (using `(t : ℂ)`
for `t : ℝ`) is included as a convenience; no `Real.log` content is
introduced at this layer.

Jensen / zero-density / sample-density input is *not* touched here.
-/

noncomputable section

namespace GaussianWhoWhere

/-- Translation defect of `Q` at shift `a` and eigenvalue `A`:

`translationDefect Q a A z = Q(z + a) − A · Q(z)`.

In the intended application `a = log p`, `A = Q(log p)`, giving the
prime-log residue `R_p(z)`. -/
def translationDefect (Q : ℂ → ℂ) (a A : ℂ) : ℂ → ℂ :=
  fun z => Q (z + a) - A * Q z

/-- **Closure under translation defects.** If `Q` has finite
exponential type, so does the defect `R_{a,A}(z) = Q(z + a) − A · Q(z)`,
for any shift `a` and any constant eigenvalue `A`. -/
theorem finiteExpType_translationDefect
    {Q : ℂ → ℂ} (hQ : FiniteExpType Q) (a A : ℂ) :
    FiniteExpType (translationDefect Q a A) := by
  unfold translationDefect
  exact finiteExpType_sub
    (finiteExpType_translate hQ a)
    (finiteExpType_const_mul hQ A)

/-- Real-shift specialization of `translationDefect` with a positive
real `t : ℝ` (lifted to `ℂ`) and eigenvalue `Q(t : ℂ)`.

We keep this real-shift form separate from actual primes to avoid
number-theoretic overhead (positivity, `Real.log_mul` etc.) at this
layer. -/
def realLogShiftDefect (Q : ℂ → ℂ) (t : ℝ) : ℂ → ℂ :=
  translationDefect Q (t : ℂ) (Q (t : ℂ))

/-- The real-shift defect inherits finite exponential type from `Q`. -/
theorem finiteExpType_realLogShiftDefect
    {Q : ℂ → ℂ} (hQ : FiniteExpType Q) (t : ℝ) :
    FiniteExpType (realLogShiftDefect Q t) := by
  unfold realLogShiftDefect
  exact finiteExpType_translationDefect hQ (t : ℂ) (Q (t : ℂ))

end GaussianWhoWhere
