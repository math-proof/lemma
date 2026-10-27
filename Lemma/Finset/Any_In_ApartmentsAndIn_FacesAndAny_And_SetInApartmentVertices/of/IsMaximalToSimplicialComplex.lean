import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.Building.Infinity.ChamberSectorConfig
open ChamberComplex AffineBuilding


namespace AffineBuilding

/--
[chamber_sector_common_apartment_thm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/ChamberSectorConfig.lean)
-/
@[path]
lemma chamber_sector_common_apartment_thm
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {si : SectorInfrastructure b}
  {C : Finset V}
  {S : Sector b}
-- given
  (hC : b.toSimplicialComplex.IsMaximal C) :
-- imply
  ∃ (A : SimplicialComplex V), A ∈ b.apartmentSystem.apartments ∧ C ∈ A.faces ∧ ∃ (S' : Sector b), Sector.Subsector b S' S ∧ SetInApartment A S'.vertices :=
-- proof
  si.chamber_sector_common_apartment C hC S

end AffineBuilding

namespace AffineBuilding

/--
[simplex_image_eq_of_fixes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/ChamberSectorConfig.lean)
-/
@[path]
lemma simplex_image_eq_of_fixes
  {V : Type}
  [DecidableEq V]
  {K L : SimplicialComplex V}
  {φ : SimplicialMap K L}
  {s : Finset V}
-- given
  (hfix : ∀ v ∈ s, φ.toFun v = v) :
-- imply
  s.image φ.toFun = s := by
-- proof
  ext x
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [hfix y hy]
  · intro hx
    exact ⟨x, hx, hfix x hx⟩

end AffineBuilding

namespace AffineBuilding

/--
[face_in_codomain_of_fixes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/ChamberSectorConfig.lean)
-/
@[path]
lemma face_in_codomain_of_fixes
  {V : Type}
  [DecidableEq V]
  {K L : SimplicialComplex V}
  {φ : SimplicialMap K L}
  {s : Finset V}
-- given
  (hs : s ∈ K.faces)
  (hfix : ∀ v ∈ s, φ.toFun v = v) :
-- imply
  s ∈ L.faces := by
-- proof
  have h := φ.map_face s hs
  rwa [simplex_image_eq_of_fixes φ s hfix] at h

end AffineBuilding

namespace AffineBuilding

/--
[image_ssubset_of_ssubset_of_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/Infinity/ChamberSectorConfig.lean)
-/
@[path]
lemma image_ssubset_of_ssubset_of_injective
  {V : Type}
  [DecidableEq V]
  {K L : SimplicialComplex V}
  {φ : SimplicialMap K L}
  {s t : Finset V}
-- given
  (hinj : Function.Injective φ.toFun)
  (hs : s ∈ K.faces)
  (ht : t ∈ K.faces)
  (hst : s ⊂ t) :
-- imply
  s.image φ.toFun ⊂ t.image φ.toFun :=
-- proof
  (Finset.image_ssubset_image hinj).mpr hst

end AffineBuilding


-- created on 2026-10-23
