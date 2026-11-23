import Def.FLTPrelim_Ramification
import Lemma.WeierstrassCurve.FreyPackageGaloisRep
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.Valuation.LocalSubring

set_option autoImplicit false

open IsLocalRing


namespace WeierstrassCurve

variable {L : Type*} [Field L] {A : ValuationSubring L}

variable (W : WeierstrassCurve A)

variable {W}

open Classical in

noncomputable def reducePoint (hΔ : (W.map (residue A)).Δ ≠ 0) :
    (W.map A.subtype).toAffine.Point → (W.map (residue A)).toAffine.Point
  | .zero => .zero
  | .some x y h =>
    if hx : x ∈ A then
      .some (residue A ⟨x, hx⟩) (residue A ⟨y, Affine.Y_mem_of_X_mem W h.1 hx⟩)
        (Affine.nonsingular_residue W hΔ h.1)
    else
      .zero

variable (hΔ : (W.map (residue A)).Δ ≠ 0)


end WeierstrassCurve
