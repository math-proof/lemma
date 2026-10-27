import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.Building.MaximalApartments.Part2
import Lemma.Bijective.All_EqImage.of.EqImage.All_IffIn_Faces_InImageFaces.Bijective.IsMaximalToSimplicialComplexToChamberComplex.In_Faces.In_Apartments
open scoped Classical


/--
[section_4_4_corollary_same_system](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AptCommonChamber.lean)
-/
@[path]
lemma section_4_4_corollary_same_system
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {L : Type}
  [DecidableEq L]
  {𝒜 : ApartmentSystem b.toChamberComplex}
  {A : SimplicialComplex V}
  {A' : SimplicialComplex V}
  {C : Finset V}
  {lab : Labelling b.toChamberComplex.toSimplicialComplex L}
-- given
  (hA : A ∈ 𝒜.apartments)
  (hA' : A' ∈ 𝒜.apartments)
  (hCmax : A.IsMaximal C)
  (hCA' : C ∈ A'.faces) :
-- imply
  (∃ φ : SimplicialMap A A', (∀ v, (∃ s ∈ A.faces, v ∈ s) → (∃ t ∈ A'.faces, v ∈ t) → φ.toFun v = v) ∧ (∀ s ∈ A.faces, lab.labelMap (s.image φ.toFun) = lab.labelMap s)) ∧ (∀ (φ : SimplicialMap A A'), Function.Bijective φ.toFun → (∀ v, (∃ s ∈ A.faces, v ∈ s) → (∃ t ∈ A'.faces, v ∈ t) → φ.toFun v = v) → ∀ s ∈ A.faces, lab.labelMap (s.image φ.toFun) = lab.labelMap s) :=
-- proof
  section_4_4_corollary b 𝒜 𝒜 A hA A' hA' C hCmax hCA' lab


-- created on 2026-10-23
