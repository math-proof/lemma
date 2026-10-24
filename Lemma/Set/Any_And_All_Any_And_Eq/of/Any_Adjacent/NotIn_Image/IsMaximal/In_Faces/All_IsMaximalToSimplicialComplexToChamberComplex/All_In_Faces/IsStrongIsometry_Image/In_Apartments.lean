import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.Building.StrongIsometryExt
import Lemma.Finset.Any_All_In_FacesAndIsMaximalAndAll_EqAndAll_EqDeltaSAndAll_EqDeltaSAndAll_EqOrAdjacent.of.IsMaximal.In_ApartmentsApartmentSystem


/--
[lemma_one_step_extension](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/SubsetsOfApartments.lean)
-/
@[path]
lemma lemma_one_step_extension
  [DecidableEq V]
  {b : Building V}
  {δW : Building.WValuedDist b}
  {A : SimplicialComplex V}
  {Y : Set (Finset V)}
  {f : Finset V → Finset V}
  {C' : Finset V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (hf_strong : IsStrongIsometry δW Y (f '' Y) f)
  (hf_img_in_A : ∀ C ∈ Y, f C ∈ A.faces)
  (hY_chambers : ∀ C ∈ Y, b.toChamberComplex.toSimplicialComplex.IsMaximal C)
  (hC'_in_A : C' ∈ A.faces)
  (hC'_maximal : A.IsMaximal C')
  (hC'_not_in_fY : C' ∉ f '' Y)
  (hC'_adj : ∃ D ∈ f '' Y, A.Adjacent C' D) :
-- imply
  ∃ (g : Finset V → Finset V), IsStrongIsometry δW (f '' Y ∪ {C'}) (g '' (f '' Y ∪ {C'})) g ∧ (∀ x ∈ f '' Y, ∃ y ∈ Y, f y = x ∧ g x = y) :=
-- proof
  strong_isometry_one_step_extension δW hA hf_strong hf_img_in_A hY_chambers
    hC'_in_A hC'_maximal hC'_not_in_fY hC'_adj


-- created on 2026-10-23
