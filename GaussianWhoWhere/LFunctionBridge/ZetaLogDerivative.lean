import GaussianWhoWhere.LFunctionBridge.ZetaEulerProduct

/-!
# Concrete `LogDerivativeBridge` witness for `riemannZeta`

This file supplies the first concrete, Mathlib-backed
`LogDerivativeBridge` value for the Riemann zeta function,
using Mathlib's

```
ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div :
  ∀ {s : ℂ}, 1 < s.re →
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s
      = -deriv riemannZeta s / riemannZeta s
```

The Bridge A′ shape `LogDerivativeBridge riemannZeta L` asks for
a model that agrees with `L` on a domain.  We pick

- the parameter `L` to be the **von Mangoldt L-series**
  `LSeries (Λ : ℂ → ...)` — the arithmetic-side companion of
  `riemannZeta`,
- the bridge's `model` field to be the **analytic
  log-derivative** `s ↦ -deriv riemannZeta s / riemannZeta s` —
  the analytic-side companion,
- the `eqOn` field discharged by Mathlib's theorem above.

The two functions agree on the right half-plane `Re(s) > 1` by
Mathlib; that is the entire content of the bridge.

No analytic continuation beyond the right half-plane, no
zero-location statement, no RH, and no Selberg-class content
are claimed.  `logDerivativeSocket` is left as `True` to keep
the bridge's `Prop` content minimal.
-/

noncomputable section

namespace GaussianWhoWhere
namespace LFunctionBridge

/-- The log-derivative bridge's domain for `riemannZeta`: the
right half-plane `{s : ℂ | 1 < s.re}`.  Identical to the
Dirichlet and Euler domains. -/
def zetaLogDerivDomain : Set ℂ :=
  ZetaBridge.rightHalfPlane_gt_one

/-- The **von Mangoldt L-series** model.  This is the
arithmetic-side companion that the Bridge A′ relation pairs
with `riemannZeta`. -/
def zetaVonMangoldtModel (s : ℂ) : ℂ :=
  LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s

/-- The **analytic log-derivative** model:
`s ↦ -ζ'(s) / ζ(s)`.  This is the analytic-side companion of
`riemannZeta` used as the `model` field of the Bridge A′ bridge
below. -/
def zetaLogDerivativeModel (s : ℂ) : ℂ :=
  -deriv riemannZeta s / riemannZeta s

/-- **Concrete Mathlib-backed `LogDerivativeBridge` instance for
`riemannZeta`.**  The parameter `L` is the von Mangoldt L-series
(`zetaVonMangoldtModel`); the bridge's `model` field is the
analytic log-derivative (`zetaLogDerivativeModel`); the `eqOn`
field is discharged by
`ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`
on the right half-plane `Re(s) > 1`.

`LogDerivativeBridge` is a `Type`, so this is a `def`. -/
def riemannZeta_logDerivativeBridge :
    LogDerivativeBridge riemannZeta zetaVonMangoldtModel :=
  { domain := zetaLogDerivDomain
    model := zetaLogDerivativeModel
    domain_nonempty := by
      refine ⟨(2 : ℂ), ?_⟩
      change (1 : ℝ) < (2 : ℂ).re
      simp
    logDerivativeSocket := True
    eqOn := by
      intro s hs
      have hs' : (1 : ℝ) < s.re := hs
      simpa [zetaVonMangoldtModel, zetaLogDerivativeModel] using
        ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
          hs' }

/-- The `riemannZeta` log-derivative bridge, projected into the
existing `Prop`-side `BridgeAprime_LogDerivLike` predicate of
`ZetaBridge.Basic`.  This is the first concrete instance of
that predicate for `riemannZeta`, paired with the von Mangoldt
L-series as the companion. -/
theorem riemannZeta_bridgeAprime_logDerivative :
    ZetaBridge.BridgeAprime_LogDerivLike
      riemannZeta zetaVonMangoldtModel :=
  logDerivativeBridge_to_BridgeAprime_LogDerivLike
    riemannZeta_logDerivativeBridge

end LFunctionBridge
end GaussianWhoWhere
