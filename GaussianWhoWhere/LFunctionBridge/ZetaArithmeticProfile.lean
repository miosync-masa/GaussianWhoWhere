import GaussianWhoWhere.LFunctionBridge.ZetaLogDerivative

/-!
# Arithmetic-only `riemannZeta` bridge profile

`ZetaBridge.ZetaBridgeCProfile` requires four ingredients: the
three arithmetic-side layers (Dirichlet, Euler product, log-
derivative) **and** the completed Where layer.  All three
arithmetic-side layers now have concrete Mathlib-backed
witnesses for `riemannZeta` (declared in
`LFunctionBridge.Basic`, `LFunctionBridge.ZetaEulerProduct`,
and `LFunctionBridge.ZetaLogDerivative`).  The completed Where
witness for `riemannZeta` (i.e. an `s ↦ Λ(s)` companion
satisfying `CompletedWhereLike`) is **not** supplied here.

This file therefore bundles only the **arithmetic / A′** part
of the zeta-side Bridge C scaffold: the three concrete bridges
above, in a single record.  It is *not* a `ZetaBridgeCProfile`
instance; it is the strictly weaker bundle that the current
witnesses can honestly fill.

A bundled `ZetaBridgeCProfile riemannZeta` is the next refinement
step and is deliberately deferred until a concrete completed
Where companion is available.

No new mathematical content.  No analytic continuation beyond
the right half-plane, no zero-location statement, no RH, no
completed Where claim, no Selberg-class content.
-/

noncomputable section

namespace GaussianWhoWhere
namespace LFunctionBridge

/-- The arithmetic-only zeta Bridge C bundle for `riemannZeta`.

Bundles the three concrete arithmetic-side bridges:

- the `Prop`-side Dirichlet-series witness
  `ZetaBridge.BridgeA_DirichletLike riemannZeta`;
- the `Type`-side Euler-product bridge
  `EulerProductBridge riemannZeta`;
- the `Type`-side logarithmic-derivative bridge
  `LogDerivativeBridge riemannZeta zetaVonMangoldtModel`.

The completed Where layer is **not** included: this bundle is
intentionally weaker than `ZetaBridge.ZetaBridgeCProfile`. -/
structure ZetaArithmeticBridgeProfile where
  dirichlet : ZetaBridge.BridgeA_DirichletLike riemannZeta
  eulerProduct : EulerProductBridge riemannZeta
  logDerivative : LogDerivativeBridge riemannZeta zetaVonMangoldtModel

/-- Concrete instance assembling the three Mathlib-backed
arithmetic-side bridges for `riemannZeta`. -/
def riemannZeta_arithmeticBridgeProfile : ZetaArithmeticBridgeProfile :=
  { dirichlet := ZetaBridge.riemannZeta_bridgeA_dirichlet
    eulerProduct := riemannZeta_eulerProductBridge
    logDerivative := riemannZeta_logDerivativeBridge }

/-! ## Projection definitions -/

/-- Project the Dirichlet-series Prop-side witness. -/
def riemannZeta_arithmeticProfile_has_dirichlet
    (P : ZetaArithmeticBridgeProfile) :
    ZetaBridge.BridgeA_DirichletLike riemannZeta :=
  P.dirichlet

/-- Project the Euler-product Type-side bridge. -/
def riemannZeta_arithmeticProfile_has_eulerProduct
    (P : ZetaArithmeticBridgeProfile) :
    EulerProductBridge riemannZeta :=
  P.eulerProduct

/-- Project the log-derivative Type-side bridge. -/
def riemannZeta_arithmeticProfile_has_logDerivative
    (P : ZetaArithmeticBridgeProfile) :
    LogDerivativeBridge riemannZeta zetaVonMangoldtModel :=
  P.logDerivative

/-- Project the Euler-product Prop-side witness, obtained by
forgetting the typed `EulerProductBridge` into
`BridgeA_EulerProductLike`. -/
def riemannZeta_arithmeticProfile_has_eulerProductProp
    (P : ZetaArithmeticBridgeProfile) :
    ZetaBridge.BridgeA_EulerProductLike riemannZeta :=
  eulerProductBridge_to_BridgeA_EulerProductLike P.eulerProduct

/-- Project the log-derivative Prop-side witness, obtained by
forgetting the typed `LogDerivativeBridge` into
`BridgeAprime_LogDerivLike`. -/
def riemannZeta_arithmeticProfile_has_logDerivativeProp
    (P : ZetaArithmeticBridgeProfile) :
    ZetaBridge.BridgeAprime_LogDerivLike
      riemannZeta zetaVonMangoldtModel :=
  logDerivativeBridge_to_BridgeAprime_LogDerivLike P.logDerivative

end LFunctionBridge
end GaussianWhoWhere
