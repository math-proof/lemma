import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Lemma.AlgebraicGeometry.NeronModelPropertyBundleCarrier
import Lemma.AlgebraicGeometry.RelativeGroupLaw
import Structure.JacJ1Iface

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

open NeronModelInfra

namespace GoodReductionJacobian

section AbstractCarriers

variable (R : Type u) [CommRing R]

def trivialPic0Designation {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) :
    RelativePic0Designation R c where
  P := Spec (CommRingCat.of R)
  toBase := 𝟙 _
  zeroSection := 𝟙 _
  zeroSection_toBase := Category.comp_id _

end AbstractCarriers

section AvatarBridge

variable {R : Type u} [CommRing R]
variable {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}

namespace AvatarSchemeBridge

variable {A : Type*} [AddCommGroup A]
variable {D : RelativePic0Designation R c} {L : RelativeGroupLaw R D.toBase}
variable {T : Scheme.{u}} {σ : T ⟶ Spec (CommRingCat.of R)}


end AvatarSchemeBridge

end AvatarBridge

end GoodReductionJacobian

namespace MilneJVScheme

open GoodReductionJacobian

variable {k : Type u} [Field k]

def JacobianSchemeData.ofCore (A : Type*) [AddCommGroup A]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) (g : ℕ)
    {J : Scheme.{u}} (f : J ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f)
    (pts : A ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
    (pts_add : ∀ x y : A, pts (x + y) = L.mul (𝟙 (Spec (CommRingCat.of k))) (pts x) (pts y))
    (hsmooth : Smooth f) (hproper : IsProper f)
    (hconn : ∀ s : Spec (CommRingCat.of k), _root_.IsConnected (f.base ⁻¹' {s})) :
    JacobianSchemeData A c g (𝟙 (Spec (CommRingCat.of k))) where
  D :=
    { P := J
      toBase := f
      zeroSection := (pts 0).1
      zeroSection_toBase := (pts 0).2 }
  L := L
  bridge :=
    { pts := pts
      pts_add := pts_add
      pts_zero := (Category.id_comp _).symm }
  hAbel :=
    { smooth := hsmooth
      proper := hproper
      connectedFibres := hconn
      hasGroupLaw := ⟨L⟩ }
  hDim := True

end MilneJVScheme
