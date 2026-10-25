import Lemma.ModularCurve.MultCoveringCharts
import Lemma.ModularCurve.JWidth
import Abbrev.ModularCurve_MultCoveringAnnuli
import Structure.ModularCurve_MultCoveringAnnuli

set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve

namespace ModularCurve.MultCovering

variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]


namespace AnnCtx

variable {Γ : ChartCtx p A} (Δ : AnnCtx Γ)


theorem twoEnded (e : Fin (mAnnuli p)) :
    (Δ.annOut e).dom = (Δ.annIn e).dom ∧ (Δ.annOut e).modulus = (Δ.annIn e).modulus ∧
      ((Δ.annIn e).modulus : AlgebraicClosure ℚ) ≠ 0 ∧
      (Δ.annOut e).param * (Δ.annIn e).param
        = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) ((Δ.annIn e).modulus : AlgebraicClosure ℚ) :=
  ⟨Δ.dom_eq e, Δ.modulus_eq' e, Δ.modulus_ne_zero e, Δ.param_mul_param e⟩

theorem attached (e : Fin (mAnnuli p)) :
    (Δ.annIn e).IsAttached (chart Γ (src p e)) (nodeSrc Γ e) ∧
      (Δ.annOut e).IsAttached (chart Γ (tgt p e)) (nodeTgt Γ e) :=
  ⟨Δ.attached_src e, Δ.attached_tgt e⟩

end AnnCtx

end ModularCurve.MultCovering
