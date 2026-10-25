import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.Buildings.code.Building.AptThinness.Part2
open ChamberComplex AptIsCoxeterProof


/--
[apt_face_in_chamber](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AptThinness.lean)
-/
@[path]
private lemma apt_face_in_chamber_eq
  [DecidableEq V]
  {K : ChamberComplex V}
  {pre : PreApartmentData K}
  {A : SimplicialComplex V}
  {s : Finset V}
-- given
  (hA : A ∈ pre.apartments)
  (hs : s ∈ A.faces) :
-- imply
  ∃ C, A.IsMaximal C ∧ s ⊆ C := by
-- proof
  apply AptIsCoxeterProof.apt_face_in_chamber pre A hA s hs

private lemma apt_gallery_connected_eq
  [DecidableEq V]
  {K : ChamberComplex V}
  {pre : PreApartmentData K}
  {A : SimplicialComplex V}
  {C D : Finset V}
-- given
  (hA : A ∈ pre.apartments)
  (hC : A.IsMaximal C)
  (hD : A.IsMaximal D) :
-- imply
  ∃ g : Gallery A, g.chambers.head? = some C ∧ g.chambers.getLast? = some D := by
-- proof
  apply AptIsCoxeterProof.apt_gallery_connected pre A hA C D hC hD

private lemma aptChamberComplex_eq_eq
  [DecidableEq V]
  {K : ChamberComplex V}
  {pre : PreApartmentData K}
  {A : SimplicialComplex V}
-- given
  (hA : A ∈ pre.apartments) :
-- imply
  (aptChamberComplex pre A hA).toSimplicialComplex = A := by
-- proof
  apply AptIsCoxeterProof.aptChamberComplex_eq pre A hA

private lemma apt_is_thin_eq
  [DecidableEq V]
  {K : ChamberComplex V}
  {pre : PreApartmentData K}
  {A : SimplicialComplex V}
-- given
  (hA : A ∈ pre.apartments) :
-- imply
  (aptChamberComplex pre A hA).IsThin := by
-- proof
  apply AptIsCoxeterProof.apt_is_thin pre A hA

private lemma apt_thinness_from_thickness_eq
  [DecidableEq V]
  {K : ChamberComplex V}
  {pre : PreApartmentData K}
  {A : SimplicialComplex V}
-- given
  (_hThick : K.IsThick)
  (hA : A ∈ pre.apartments) :
-- imply
  ∃ (cc : ChamberComplex V), cc.toSimplicialComplex = A ∧ cc.IsThin := by
-- proof
  apply AptIsCoxeterProof.apt_thinness_from_thickness K _hThick pre A hA


-- created on 2026-10-24
