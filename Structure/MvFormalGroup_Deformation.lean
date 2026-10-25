import Class.MvFormalGroup_BasicV2

set_option autoImplicit false

noncomputable section

namespace MvFormalGroup

@[ext]
structure Deformation {S : Type} [CommRing S] {d : ℕ} (G₀ : MvFormalGroup d S)
    (B : Type) [CommRing B] [Algebra B S] : Type where

  F : MvFormalGroup d B

  map_eq : F.map (algebraMap B S) = G₀

namespace Deformation

variable {S : Type} [CommRing S] {d : ℕ} {G₀ : MvFormalGroup d S} {B : Type} [CommRing B] [Algebra B S]


end Deformation

end MvFormalGroup

end
