import Mathlib
import Lemma.Definitions.Def_Deformations_ProartinianCat

set_option autoImplicit false

universe u

namespace Deformation

open CategoryTheory IsLocalRing ProartinianCat

local notation3:max "𝓴" 𝓞:max => (IsLocalRing.ResidueField 𝓞)

namespace ProartinianCat

variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]
variable {R : ProartinianCat 𝓞}

variable (R) in

noncomputable def residueMap (r : R) : 𝓴 𝓞 := (toResidueField R).hom r

lemma residueMap_one : residueMap R (1 : R) = 1 := map_one (toResidueField R).hom

lemma residueMap_mul (r s : R) : residueMap R (r * s) = residueMap R r * residueMap R s :=
  map_mul (toResidueField R).hom r s

lemma residueMap_add (r s : R) : residueMap R (r + s) = residueMap R r + residueMap R s :=
  map_add (toResidueField R).hom r s

lemma residueMap_zero : residueMap R (0 : R) = 0 := map_zero (toResidueField R).hom

lemma residueMap_algebraMap (o : 𝓞) :
    residueMap R (algebraMap 𝓞 R o) = algebraMap 𝓞 (𝓴 𝓞) o :=
  (toResidueField R).hom.commutes o

lemma residueMap_eq_zero_of_mem {r : R} (hr : r ∈ maximalIdeal R) : residueMap R r = 0 := by
  show (toResidueField R).hom r = 0
  rw [← RingHom.mem_ker, ker_toResidueField R]
  exact hr

lemma isLocallyConstant_residueMap : IsLocallyConstant (residueMap R) :=
  (IsLocallyConstant.iff_continuous
    ((toResidueField R).hom : R → (residueField (𝓞 := 𝓞)))).mpr (toResidueField R).hom.cont

variable (R) in

structure IsTangentVector (D : R → 𝓴 𝓞) : Prop where
  map_add : ∀ r s, D (r + s) = D r + D s
  leibniz : ∀ r s, D (r * s) = residueMap R r * D s + D r * residueMap R s
  map_algebraMap : ∀ o : 𝓞, D (algebraMap 𝓞 R o) = 0
  isLocallyConstant : IsLocallyConstant D

namespace IsTangentVector

variable {D : R → 𝓴 𝓞} (hD : IsTangentVector R D)

include hD

lemma map_zero : D 0 = 0 := by
  have h := (hD.map_add 0 0).symm
  rw [add_zero] at h
  exact add_left_cancel (h.trans (add_zero (D 0)).symm)

lemma map_one : D 1 = 0 := by simpa using hD.map_algebraMap 1

end IsTangentVector

variable (R) in

def tangentSubmodule : Submodule (𝓴 𝓞) (R → 𝓴 𝓞) where
  carrier := {D | IsTangentVector R D}
  zero_mem' :=
    { map_add := fun _ _ => (add_zero (0 : 𝓴 𝓞)).symm
      leibniz := fun r s => by simp
      map_algebraMap := fun _ => rfl
      isLocallyConstant := IsLocallyConstant.const 0 }
  add_mem' := by
    rintro D D' hD hD'
    exact
      { map_add := fun r s => by
          simp only [Pi.add_apply, hD.map_add, hD'.map_add]; ring
        leibniz := fun r s => by
          simp only [Pi.add_apply, hD.leibniz, hD'.leibniz]; ring
        map_algebraMap := fun o => by
          simp only [Pi.add_apply, hD.map_algebraMap, hD'.map_algebraMap, add_zero]
        isLocallyConstant :=
          IsLocallyConstant.comp₂ hD.isLocallyConstant hD'.isLocallyConstant (· + ·) }
  smul_mem' := by
    rintro c D hD
    exact
      { map_add := fun r s => by
          simp only [Pi.smul_apply, hD.map_add, smul_eq_mul]; ring
        leibniz := fun r s => by
          simp only [Pi.smul_apply, hD.leibniz, smul_eq_mul]; ring
        map_algebraMap := fun o => by
          simp only [Pi.smul_apply, hD.map_algebraMap, smul_zero]
        isLocallyConstant := hD.isLocallyConstant.comp (c • ·) }

@[simp]
lemma mem_tangentSubmodule {D : R → 𝓴 𝓞} : D ∈ tangentSubmodule R ↔ IsTangentVector R D :=
  Iff.rfl

end ProartinianCat

end Deformation
