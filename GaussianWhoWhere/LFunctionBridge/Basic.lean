import GaussianWhoWhere.ZetaBridge.Basic

/-!
# General L-function Bridge C profile (`LFunctionBridge.Basic`)

This file is a **Type-side refinement layer** over the existing
`Prop`-side `ZetaBridge` scaffold of
`GaussianWhoWhere/ZetaBridge/Basic.lean`.  It does not change any
existing predicate, profile, or theorem in `ZetaBridge`; it adds
named `structure`-shaped bridges (`DirichletSeriesBridge`,
`EulerProductBridge`, `LogDerivativeBridge`) that carry data
together with a socket `Prop` field, and packages them into a
new generic profile `LFunctionBridgeCProfile`.

The point of this layer is methodological:

- The existing `BridgeA_EulerProductLike` is only an existential
  `Prop`.  V's first concrete Euler-product structurization is
  `EulerProductBridge`, which exposes the local factor, the
  product model, and a named `eulerProductSocket : Prop`.
- The new `SelbergClassLike` interface gives a typed supplier of
  `LFunctionBridgeCProfile` extended with two further sockets
  (analytic continuation and Ramanujan) that any future Selberg-
  class-style formalization could populate.

No mathematics is proved here.  The Selberg class is not
formalized; analytic continuation, the Ramanujan conjecture, the
Euler product for `riemannZeta`, the Bridge A′ log-derivative
passage, and any zero-location statement remain open.  All
`Prop` fields are sockets, not proofs.
-/

noncomputable section

namespace GaussianWhoWhere
namespace LFunctionBridge

/-! ## Typed bridge structures

Each of the three bridges below carries (i) a nonempty domain,
(ii) a model function, (iii) a socket `Prop` field naming the
analytic content the bridge is intended to carry, and (iv) an
`EqOn` agreement between the target function and the model on
the domain.  The socket field is **not** discharged here. -/

/-- Typed Dirichlet-series bridge for an `L`-function-like
target `F : ℂ → ℂ`. -/
structure DirichletSeriesBridge (F : ℂ → ℂ) where
  domain : Set ℂ
  coefficients : ℕ → ℂ
  seriesModel : ℂ → ℂ
  domain_nonempty : domain.Nonempty
  dirichletSeriesSocket : Prop
  eqOn : Set.EqOn F seriesModel domain

/-- Typed Euler-product bridge for an `L`-function-like target
`F : ℂ → ℂ`.

This is the first actual Euler-product **structurization** in
the package: instead of an existential `Prop` (as in
`ZetaBridge.BridgeA_EulerProductLike`), the bridge carries the
local-factor family and the product model as data, together
with a named `eulerProductSocket : Prop` for the intended
analytic content. -/
structure EulerProductBridge (F : ℂ → ℂ) where
  domain : Set ℂ
  localFactor : ℕ → ℂ → ℂ
  productModel : ℂ → ℂ
  domain_nonempty : domain.Nonempty
  eulerProductSocket : Prop
  eqOn : Set.EqOn F productModel domain

/-- Typed logarithmic-derivative bridge.

`LogDerivativeBridge F L` carries a nonempty domain, a model
function for the log-derivative companion `L`, and a named
`logDerivativeSocket : Prop` recording the intended Bridge A′
content.  No log-derivative is computed here. -/
structure LogDerivativeBridge (_F L : ℂ → ℂ) where
  domain : Set ℂ
  model : ℂ → ℂ
  domain_nonempty : domain.Nonempty
  logDerivativeSocket : Prop
  eqOn : Set.EqOn L model domain

/-! ## Forgetful maps to the existing `ZetaBridge` predicates

Each typed bridge forgets to the corresponding existential
`Prop` of `ZetaBridge`.  The reverse direction is not derivable
and is not provided. -/

/-- A typed Dirichlet bridge supplies the `Prop`-side
`BridgeA_DirichletLike`. -/
def dirichletSeriesBridge_to_BridgeA_DirichletLike
    {F : ℂ → ℂ} (b : DirichletSeriesBridge F) :
    ZetaBridge.BridgeA_DirichletLike F :=
  ⟨b.domain, b.seriesModel, b.domain_nonempty, b.eqOn⟩

/-- A typed Euler-product bridge supplies the `Prop`-side
`BridgeA_EulerProductLike`. -/
def eulerProductBridge_to_BridgeA_EulerProductLike
    {F : ℂ → ℂ} (b : EulerProductBridge F) :
    ZetaBridge.BridgeA_EulerProductLike F :=
  ⟨b.domain, b.productModel, b.domain_nonempty, b.eqOn⟩

/-- A typed logarithmic-derivative bridge supplies the
`Prop`-side `BridgeAprime_LogDerivLike`. -/
def logDerivativeBridge_to_BridgeAprime_LogDerivLike
    {F L : ℂ → ℂ} (b : LogDerivativeBridge F L) :
    ZetaBridge.BridgeAprime_LogDerivLike F L :=
  ⟨b.domain, b.model, b.domain_nonempty, b.eqOn⟩

/-! ## Generic L-function Bridge C profile

`LFunctionBridgeCProfile` packages the three typed bridges
above together with the completed Where layer.  It is the
Type-side counterpart of `ZetaBridge.ZetaBridgeCProfile`. -/

/-- A generic L-function Bridge C profile, packaging the three
typed bridges plus the completed Where layer. -/
structure LFunctionBridgeCProfile where
  L : ℂ → ℂ
  completedL : ℂ → ℂ
  logDeriv : ℂ → ℂ
  dirichlet : DirichletSeriesBridge L
  eulerProduct : EulerProductBridge L
  logDerivative : LogDerivativeBridge L logDeriv
  where_completed : ZetaBridge.CompletedWhereLike completedL

/-! ### Projection definitions -/

/-- Project the Dirichlet-series bridge out of an
`LFunctionBridgeCProfile`. -/
def lFunctionBridgeCProfile_has_dirichlet
    (P : LFunctionBridgeCProfile) :
    DirichletSeriesBridge P.L :=
  P.dirichlet

/-- Project the Euler-product bridge out of an
`LFunctionBridgeCProfile`. -/
def lFunctionBridgeCProfile_has_eulerProduct
    (P : LFunctionBridgeCProfile) :
    EulerProductBridge P.L :=
  P.eulerProduct

/-- Project the logarithmic-derivative bridge out of an
`LFunctionBridgeCProfile`. -/
def lFunctionBridgeCProfile_has_logDerivative
    (P : LFunctionBridgeCProfile) :
    LogDerivativeBridge P.L P.logDeriv :=
  P.logDerivative

/-- Project the completed-Where condition out of an
`LFunctionBridgeCProfile`. -/
def lFunctionBridgeCProfile_has_where
    (P : LFunctionBridgeCProfile) :
    ZetaBridge.CompletedWhereLike P.completedL :=
  P.where_completed

/-- Convert an `LFunctionBridgeCProfile` into the existing
`Prop`-side `ZetaBridge.ZetaBridgeCProfile`.  This is the
forgetful direction; no reverse conversion is provided. -/
def lFunctionBridgeCProfile_to_zetaBridgeCProfile
    (P : LFunctionBridgeCProfile) :
    ZetaBridge.ZetaBridgeCProfile :=
  { zetaLike := P.L
    completedLike := P.completedL
    logDerivLike := P.logDeriv
    bridgeA_dirichlet :=
      dirichletSeriesBridge_to_BridgeA_DirichletLike P.dirichlet
    bridgeA_euler :=
      eulerProductBridge_to_BridgeA_EulerProductLike P.eulerProduct
    bridgeAprime :=
      logDerivativeBridge_to_BridgeAprime_LogDerivLike P.logDerivative
    where_completed := P.where_completed }

/-! ## `SelbergClassLike` interface

`SelbergClassLike` is a typed supplier of
`LFunctionBridgeCProfile` extended with two further sockets:
analytic continuation and Ramanujan.  Neither socket is proved
here.  The interface is not a formalization of the Selberg
class; it is a typed shape that a future Selberg-class
formalization could populate. -/

/-- A typed supplier of `LFunctionBridgeCProfile` carrying two
further sockets (`analyticContinuationSocket`, `ramanujanSocket`)
characteristic of Selberg-class L-functions. -/
structure SelbergClassLike where
  L : ℂ → ℂ
  completedL : ℂ → ℂ
  logDeriv : ℂ → ℂ
  dirichlet : DirichletSeriesBridge L
  eulerProduct : EulerProductBridge L
  logDerivative : LogDerivativeBridge L logDeriv
  where_completed : ZetaBridge.CompletedWhereLike completedL
  analyticContinuationSocket : Prop
  ramanujanSocket : Prop

/-- A `SelbergClassLike` value supplies a generic
`LFunctionBridgeCProfile` by forgetting the two extra Selberg
sockets. -/
def lFunctionBridgeCProfile_of_selbergClassLike
    (S : SelbergClassLike) : LFunctionBridgeCProfile :=
  { L := S.L
    completedL := S.completedL
    logDeriv := S.logDeriv
    dirichlet := S.dirichlet
    eulerProduct := S.eulerProduct
    logDerivative := S.logDerivative
    where_completed := S.where_completed }

end LFunctionBridge
end GaussianWhoWhere
