-- Carved from Lemma/Definitions/Def_Deformations_ProartinianCat.lean: instance decls only.
import Mathlib
import Instance.Deformations_IsProartinian
import Class.Deformations_IsResidueAlgebra
import Class.Deformations_ProartinianCat

set_option autoImplicit false

universe u

open CategoryTheory Function Limits IsLocalRing

namespace Deformation

variable (𝓞 : Type u) [CommRing 𝓞]


namespace ProartinianCat


instance : CoeSort (ProartinianCat 𝓞) (Type u) := ⟨carrier⟩


instance : Category (ProartinianCat 𝓞) where
  Hom A B := Hom A B
  id A := ⟨ContinuousAlgHom.id 𝓞 A⟩
  comp f g := ⟨g.hom.comp f.hom⟩

instance (A B : ProartinianCat 𝓞) (f : A ⟶ B) : IsLocalHom f.hom := by
  convert isLocalHom_of_isContinuous_of_isProartinian f.hom.toRingHom f.hom.cont
  exact ⟨fun ⟨H⟩ ↦ ⟨H⟩, fun ⟨H⟩ ↦ ⟨H⟩⟩

variable {𝓞}

variable {X Y Z : Type u}

variable {A B C : ProartinianCat 𝓞}

section self

variable [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]

instance : IsAdicTopology (self (𝓞 := 𝓞)) := ⟨rfl⟩

instance (R : ProartinianCat 𝓞) : Unique (self ⟶ R) := by
  refine ⟨⟨fromSelf R⟩, fun f ↦ ?_⟩
  ext : 1
  apply ContinuousAlgHom.coe_inj.mp
  ext

end self

section residueField

variable [IsLocalRing 𝓞]

instance : DiscreteTopology (residueField (𝓞 := 𝓞)) := ⟨rfl⟩

noncomputable
instance : Field (residueField (𝓞 := 𝓞)) := inferInstanceAs (Field (ResidueField 𝓞))

noncomputable
instance (R : ProartinianCat 𝓞) : Unique (R ⟶ residueField) := by
  refine ⟨⟨toResidueField R⟩, fun f ↦ ?_⟩
  ext
  simp [to_residueField_apply]

end residueField

end ProartinianCat

end Deformation
