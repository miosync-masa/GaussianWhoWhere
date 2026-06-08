import GaussianWhoWhere.LFunctionBridge.Basic

/-!
# Concrete `EulerProductBridge` witness for `riemannZeta`

This file supplies the first concrete, Mathlib-backed
`EulerProductBridge` value for the Riemann zeta function.

It uses Mathlib's `riemannZeta_eulerProduct_tprod`, whose type
is

```
∀ {s : ℂ}, 1 < s.re →
  ∏' (p : Nat.Primes), (1 - (p : ℂ) ^ (-s))⁻¹ = riemannZeta s
```

so the natural Type-side product model is the `Nat.Primes`-
indexed product.  The `localFactor` field of
`EulerProductBridge` is `ℕ → ℂ → ℂ`; we take it to be the
documentation-flavored definition that returns
`(1 - n^(-s))⁻¹` when `n` is prime and `1` otherwise.  This is
not used in the product model — the product model lives over
`Nat.Primes` directly, matching the Mathlib theorem.  The
`localFactor` field records the intended local-factor shape;
the actual link between local factor and product model is
deferred and is **not** asserted here.

No new mathematics is proved.  We do not internalize any
analytic continuation, RH statement, or Selberg-class content.
The `eulerProductSocket` is left as `True` to keep the bridge's
Prop content minimal; the Mathlib theorem closes only the
`eqOn` field.
-/

noncomputable section

namespace GaussianWhoWhere
namespace LFunctionBridge

/-- The Euler-product domain for `riemannZeta`: the right
half-plane `{s : ℂ | 1 < s.re}`.  Identical to the Dirichlet
domain `ZetaBridge.rightHalfPlane_gt_one`. -/
def zetaEulerDomain : Set ℂ :=
  ZetaBridge.rightHalfPlane_gt_one

/-- Documentation-flavored local-factor function for the
Riemann zeta Euler product: prime `n` maps to
`(1 - n^(-s))⁻¹`, every non-prime maps to the trivial factor
`1`.  This `ℕ → ℂ → ℂ` shape matches the
`EulerProductBridge.localFactor` field and records the local-
factor intent.  The actual product model lives over
`Nat.Primes` (see `zetaEulerProductModel`); the link between
`localFactor` and `productModel` is deferred. -/
def zetaEulerLocalFactor (n : ℕ) (s : ℂ) : ℂ :=
  if Nat.Prime n then (1 - (n : ℂ) ^ (-s))⁻¹ else 1

/-- The Euler-product model for `riemannZeta`, indexed over
`Nat.Primes` so the agreement with
`riemannZeta_eulerProduct_tprod` is direct. -/
def zetaEulerProductModel (s : ℂ) : ℂ :=
  ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹

/-- **Concrete Mathlib-backed `EulerProductBridge` instance for
`riemannZeta`.**  Uses `riemannZeta_eulerProduct_tprod` on the
right half-plane `Re(s) > 1`.  `EulerProductBridge` is a `Type`,
so this is a `def` rather than a `theorem`. -/
def riemannZeta_eulerProductBridge :
    EulerProductBridge riemannZeta :=
  { domain := zetaEulerDomain
    localFactor := zetaEulerLocalFactor
    productModel := zetaEulerProductModel
    domain_nonempty := by
      refine ⟨(2 : ℂ), ?_⟩
      change (1 : ℝ) < (2 : ℂ).re
      simp
    eulerProductSocket := True
    eqOn := by
      intro s hs
      have hs' : (1 : ℝ) < s.re := hs
      simpa [zetaEulerProductModel] using
        (riemannZeta_eulerProduct_tprod hs').symm }

/-- The `riemannZeta` Euler product, projected into the
existing `Prop`-side `BridgeA_EulerProductLike` predicate of
`ZetaBridge.Basic`.  This is the first concrete instance of
that predicate for `riemannZeta`. -/
theorem riemannZeta_bridgeA_eulerProduct :
    ZetaBridge.BridgeA_EulerProductLike riemannZeta :=
  eulerProductBridge_to_BridgeA_EulerProductLike
    riemannZeta_eulerProductBridge

end LFunctionBridge
end GaussianWhoWhere
