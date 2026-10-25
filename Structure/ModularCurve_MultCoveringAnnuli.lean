import Instance.ModularCurve_MultCoveringCharts
import Def.ModularCurve_JWidth
import Abbrev.ModularCurve_MultCoveringAnnuli

set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

namespace ModularCurve.MultCovering

variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]

structure AnnCtx (Γ : ChartCtx p A) where

  An  : Fin (mAnnuli p) → Annulus A ↥(modularFunctionFieldBar (1 * p))

  An' : Fin (mAnnuli p) → Annulus A ↥(modularFunctionFieldBar (1 * p))

  dom_eq : ∀ e, (An' e).dom = (An e).dom
  modulus_eq' : ∀ e, (An' e).modulus = (An e).modulus
  modulus_ne_zero : ∀ e, ((An e).modulus : AlgebraicClosure ℚ) ≠ 0
  param_mul_param : ∀ e, (An' e).param * (An e).param
      = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((An e).modulus : AlgebraicClosure ℚ)

  mem_dom_iff : ∀ e (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))),
      W ∈ (An e).dom ↔ IsSSCentred p A W (ssValue Γ e)

  param_eq_tieG : ∀ e, ssValue Γ e ≠ 0 → ssValue Γ e ≠ 1728 → (An e).param = tieG p

  modulus_eq : ∀ e, (An e).modulus = ((p : ℕ) : ↥A) ^ jWidth (ssValue Γ e)

  attached_src : ∀ e, (An e).IsAttached (chart Γ (src p e)) (nodeSrc Γ e)

  attached_tgt : ∀ e, (An' e).IsAttached (chart Γ (tgt p e)) (nodeTgt Γ e)

namespace AnnCtx

variable {Γ : ChartCtx p A} (Δ : AnnCtx Γ)


end AnnCtx

end ModularCurve.MultCovering
