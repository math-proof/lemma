import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.Building.StrongIsometryExt
import Lemma.Finset.Any_All_In_FacesAndIsMaximalAndAll_EqAndAll_EqDeltaSAndAll_EqDeltaSAndAll_EqOrAdjacent.of.IsMaximal.In_ApartmentsApartmentSystem


/--
[galleryDist_eq_coxeterLength](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/StrongIsometryExtMain.lean)
-/
@[path]
lemma galleryDist_eq_coxeterLength
  [DecidableEq V]
  [DecidableEq V]
  {b : Building V}
  {δW : Building.WValuedDist b}
  {C D : Finset V} :
-- imply
  galleryDist b.toChamberComplex.toSimplicialComplex C D = δW.coxeterMatrix.toCoxeterSystem.length (δW.delta C D) :=
-- proof
  δW.galleryDist_eq_length C D

private lemma delta_eq_imp_galleryDist_eq
  [DecidableEq V]
  {b : Building V}
  {δW : Building.WValuedDist b}
  {C D C' D' : Finset V} :
-- imply
  δW.delta C D = δW.delta C' D' → galleryDist b.toChamberComplex.toSimplicialComplex C D = galleryDist b.toChamberComplex.toSimplicialComplex C' D' := by
-- proof
  intro h
  rw [galleryDist_eq_coxeterLength δW C D, galleryDist_eq_coxeterLength δW C' D', h]

private lemma Building.strong_iso_ext
  [DecidableEq V]
  {b : Building V}
  {δW : Building.WValuedDist b}
  {Y : Set (Finset V)}
  {A : SimplicialComplex V}
  {f : Finset V → Finset V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (hf : IsStrongIsometry δW Y (f '' Y) f)
  (hf_img : ∀ C ∈ Y, f C ∈ A.faces) :
-- imply
  ∃ (B : SimplicialComplex V), B ∈ b.apartmentSystem.apartments ∧ ∀ C ∈ Y, C ∈ B.faces := by
-- proof
  obtain ⟨hf_map, hf_surj, hf_delta⟩ := hf
  apply b.apartmentSystem.strong_iso_ext_gallery Y (f '' Y) f
  · intro C hC
    exact Set.mem_image_of_mem f hC
  · intro C hC D hD
    exact delta_eq_imp_galleryDist_eq δW (f C) (f D) C D (hf_delta C hC D hD)
  · exact ⟨A, hA, fun C hC => by obtain ⟨D, hD, rfl⟩ := hC; exact hf_img D hD⟩


-- created on 2026-10-24
