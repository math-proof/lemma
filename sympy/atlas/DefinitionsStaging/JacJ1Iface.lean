import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Lemma.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Lemma.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Structure.JacJ1Iface
import Def.JacJ1Iface

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

open NeronModelInfra

namespace GoodReductionJacobian

section AbstractCarriers

variable (R : Type u) [CommRing R]


end AbstractCarriers

section AvatarBridge

variable {R : Type u} [CommRing R]
variable {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}

namespace AvatarSchemeBridge

variable {A : Type*} [AddCommGroup A]
variable {D : RelativePic0Designation R c} {L : RelativeGroupLaw R D.toBase}
variable {T : Scheme.{u}} {σ : T ⟶ Spec (CommRingCat.of R)}

theorem law_one_eq_pts_zero (B : AvatarSchemeBridge A D L σ) :
    L.one σ = B.pts 0 := by
  have hidem : L.mul σ (B.pts 0) (B.pts 0) = B.pts 0 := by
    rw [← B.pts_add, add_zero]
  calc L.one σ
      = L.mul σ (L.inv σ (B.pts 0)) (B.pts 0) := (L.inv_mul_cancel σ (B.pts 0)).symm
    _ = L.mul σ (L.inv σ (B.pts 0)) (L.mul σ (B.pts 0) (B.pts 0)) := by rw [hidem]
    _ = L.mul σ (L.mul σ (L.inv σ (B.pts 0)) (B.pts 0)) (B.pts 0) :=
        (L.mul_assoc σ _ _ _).symm
    _ = L.mul σ (L.one σ) (B.pts 0) := by rw [L.inv_mul_cancel]
    _ = B.pts 0 := L.one_mul σ _

end AvatarSchemeBridge

end AvatarBridge

end GoodReductionJacobian

namespace MilneJVScheme

open GoodReductionJacobian

variable {k : Type u} [Field k]


end MilneJVScheme
