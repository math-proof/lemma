import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.Building.AptIsCoxeterProof
import Lemma.Set.ApartmentsToApartmentSystem.eq.Apartments.of.IsThick
open ChamberComplex


/--
[building_max_in_apt_is_apt_max](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ThicknessAptStructureProof.lean)
-/
@[path]
lemma building_max_in_apt_is_apt_max
  [DecidableEq V]
  {K : ChamberComplex V}
  {pre : AptIsCoxeterProof.PreApartmentData K}
  {A : SimplicialComplex V}
  {C : Finset V}
-- given
  (hA : A ∈ pre.apartments)
  (hC_A : C ∈ A.faces)
  (hC_K : K.toSimplicialComplex.IsMaximal C) :
-- imply
  A.IsMaximal C :=
-- proof
  pre.building_maximal_in_apt_is_apt_maximal A hA C hC_A hC_K


private lemma apt_max_is_building_max
  [DecidableEq V]
  {K : ChamberComplex V}
  {pre : AptIsCoxeterProof.PreApartmentData K}
  {A : SimplicialComplex V}
  {C : Finset V}
-- given
  (hA : A ∈ pre.apartments)
  (hC : A.IsMaximal C) :
-- imply
  K.toSimplicialComplex.IsMaximal C :=
-- proof
  pre.maximal_in_apt_is_maximal A hA C hC


-- created on 2026-10-24
