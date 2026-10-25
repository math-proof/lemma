import Class.MvFormalGroup_BasicV2
import Structure.MvFormalGroup_Deformation

set_option autoImplicit false

noncomputable section

namespace MvFormalGroup


namespace Deformation

variable {S : Type} [CommRing S] {d : ℕ} {G₀ : MvFormalGroup d S} {B : Type} [CommRing B] [Algebra B S]

def IsIso (D D' : Deformation G₀ B) : Prop :=
  ∃ φ : MvFormalGroup.Hom D.F D'.F,
    (∃ ψ : MvFormalGroup.Hom D'.F D.F, ψ.comp φ = MvFormalGroup.Hom.id D.F ∧ φ.comp ψ = MvFormalGroup.Hom.id D'.F) ∧
    ∀ i : Fin d, MvPowerSeries.map (algebraMap B S) (φ.toPowerSeries i) = MvPowerSeries.X i

def refl (G₀ : MvFormalGroup d S) : Deformation G₀ S where
  F := G₀
  map_eq := by
    ext i n
    simp [MvFormalGroup.map, Algebra.algebraMap_self]

end Deformation

end MvFormalGroup

end
