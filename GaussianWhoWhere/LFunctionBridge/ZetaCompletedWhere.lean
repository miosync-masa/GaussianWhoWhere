import GaussianWhoWhere.LFunctionBridge.ZetaArithmeticProfile

/-!
# Concrete completed Where witness for `riemannZeta` and full
`ZetaBridgeCProfile riemannZeta` instance

This file closes the last remaining concrete-witness gap in the
C-ζ branch: the completed-Where layer.  Mathlib already supplies
both completed zeta objects and their reflection identities,
with no exceptional points and no domain restrictions:

```
completedRiemannZeta_one_sub :
  ∀ s : ℂ, completedRiemannZeta (1 - s) = completedRiemannZeta s

completedRiemannZeta₀_one_sub :
  ∀ s : ℂ, completedRiemannZeta₀ (1 - s) = completedRiemannZeta₀ s
```

Either form directly matches the `ZetaBridge.CompletedWhereLike`
predicate.  We use `completedRiemannZeta₀` as the canonical
completed-Where companion, matching the convention adopted in
the paper's discussion of the layer separation.

With this last witness in place, we can assemble a concrete
`ZetaBridge.ZetaBridgeCProfile` instance for `riemannZeta` that
binds:

- `zetaLike = riemannZeta`,
- `completedLike = completedRiemannZeta₀`,
- `logDerivLike = zetaVonMangoldtModel`,
- the three concrete arithmetic-side bridges from
  `LFunctionBridge.Basic` /
  `LFunctionBridge.ZetaEulerProduct` /
  `LFunctionBridge.ZetaLogDerivative`, and
- the new completed-Where witness defined below.

No analytic continuation beyond what Mathlib already provides,
no zero-location statement, no RH, no Selberg-class content,
and no HP ↔ ζ identification are claimed.  The only new content
of this file is the assembly of an existing Mathlib reflection
identity into the predicate shape of `CompletedWhereLike`.
-/

noncomputable section

namespace GaussianWhoWhere
namespace LFunctionBridge

/-- The completed-Where companion of `riemannZeta` used by this
file: Mathlib's `completedRiemannZeta₀`.  Bundled here as a
named `ℂ → ℂ` so that the profile field `completedLike` has a
stable identifier in `#check` output. -/
def completedZetaWhereModel : ℂ → ℂ :=
  completedRiemannZeta₀

/-- **Concrete Mathlib-backed `CompletedWhereLike` instance for
the completed zeta `completedRiemannZeta₀`.**  Discharged
directly by `completedRiemannZeta₀_one_sub`. -/
theorem completedZeta_completedWhere :
    ZetaBridge.CompletedWhereLike completedZetaWhereModel := by
  intro s
  exact completedRiemannZeta₀_one_sub s

/-- **Full concrete `ZetaBridgeCProfile` instance for
`riemannZeta`.**

All four fields are now concrete and Mathlib-backed:

- `zetaLike = riemannZeta`;
- `completedLike = completedRiemannZeta₀`;
- `logDerivLike = zetaVonMangoldtModel`
  (Mathlib's `LSeries (Λ : ℂ → ...)`);
- `bridgeA_dirichlet`, `bridgeA_euler`, `bridgeAprime`,
  `where_completed` supplied by the three arithmetic-side
  bridges of `LFunctionBridge` and the new completed-Where
  witness above.

This bundles the four concrete Mathlib-backed components into a
single `ZetaBridgeCProfile` for `riemannZeta`, closing the
"deferred bundled instance" item noted in
`docs/LeanDAG.md` and `docs/BridgeCBranches.md`. -/
def riemannZeta_zetaBridgeCProfile : ZetaBridge.ZetaBridgeCProfile :=
  { zetaLike := riemannZeta
    completedLike := completedZetaWhereModel
    logDerivLike := zetaVonMangoldtModel
    bridgeA_dirichlet := ZetaBridge.riemannZeta_bridgeA_dirichlet
    bridgeA_euler := riemannZeta_bridgeA_eulerProduct
    bridgeAprime := riemannZeta_bridgeAprime_logDerivative
    where_completed := completedZeta_completedWhere }

end LFunctionBridge
end GaussianWhoWhere
