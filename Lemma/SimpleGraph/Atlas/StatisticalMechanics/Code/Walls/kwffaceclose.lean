import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.kwffaceclose.Part3
open Finset SimpleGraph StatMech StatMech.Walls


/--
[kwf_walkEdges_iff_faceCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwffaceclose.lean)
-/
@[path]
private lemma kwf_walkEdges_iff_faceCut_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hnd : Vc.edges.Nodup)
  (huv : (hypercubicLattice 2).Adj u v) :
-- imply
  s(u, v) ∈ Vc.edges.toFinset ↔ s(u, v) ∈ jed_cutSet (fwr_faceInside Vc) := by
-- proof
  apply StatMech.Walls.kwf_walkEdges_iff_faceCut Vc hnd huv

/--
[kwf_walkParity_eq_faceParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwffaceclose.lean)
-/
@[path]
private lemma kwf_walkParity_eq_faceParity_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : Site 2}
  {p : (hypercubicLattice 2).Walk x y}
-- given
  (hnd : Vc.edges.Nodup) :
-- imply
  walkParity (hypercubicLattice 2) (Vc.edges.toFinset) p = kwf_faceParity (fwr_faceInside Vc) p := by
-- proof
  apply StatMech.Walls.kwf_walkParity_eq_faceParity Vc hnd p

/--
[kwf_latLinking_iff_faceCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwffaceclose.lean)
-/
@[path]
private lemma kwf_latLinking_iff_faceCut_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (hnd : Vc.edges.Nodup) :
-- imply
  kwf_LinkingEven (Vc.edges.toFinset) ↔ ∀ (x : Site 2) (p : (hypercubicLattice 2).Walk x x), kwf_faceParity (fwr_faceInside Vc) p = false := by
-- proof
  apply StatMech.Walls.kwf_latLinking_iff_faceCut Vc hnd

/--
[kwf_linkingEven_of_vertexCoboundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwffaceclose.lean)
-/
@[path]
private lemma kwf_linkingEven_of_vertexCoboundary_eq
  {δ : Finset (Sym2 (Site 2))}
  {c : Site 2 → Bool}
-- given
  (hδ : ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v → (s(u, v) ∈ δ ↔ c u ≠ c v)) :
-- imply
  kwf_LinkingEven δ := by
-- proof
  apply StatMech.Walls.kwf_linkingEven_of_vertexCoboundary c hδ

/--
[kwf_chord_not_cut_be](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwffaceclose.lean)
-/
@[path]
private lemma kwf_chord_not_cut_be_eq :
-- imply
  s((![1, 1] : Site 2), (![2, 1] : Site 2)) ∉ jed_cutSet jcw_shiftFace := by
-- proof
  apply StatMech.Walls.kwf_chord_not_cut_be

/--
[kwf_chord_not_cut_cf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwffaceclose.lean)
-/
@[path]
private lemma kwf_chord_not_cut_cf_eq :
-- imply
  s((![1, 2] : Site 2), (![2, 2] : Site 2)) ∉ jed_cutSet jcw_shiftFace := by
-- proof
  apply StatMech.Walls.kwf_chord_not_cut_cf

/--
[kwf_chord_not_cut_ef](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwffaceclose.lean)
-/
@[path]
private lemma kwf_chord_not_cut_ef_eq :
-- imply
  s((![2, 1] : Site 2), (![2, 2] : Site 2)) ∉ jed_cutSet jcw_shiftFace := by
-- proof
  apply StatMech.Walls.kwf_chord_not_cut_ef

/--
[kwf_faceCut_not_vertexCoboundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwffaceclose.lean)
-/
@[path]
private lemma kwf_faceCut_not_vertexCoboundary_eq :
-- imply
  ¬ ∃ c : Site 2 → Bool, ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v → (s(u, v) ∈ jed_cutSet jcw_shiftFace ↔ c u ≠ c v) := by
-- proof
  apply StatMech.Walls.kwf_faceCut_not_vertexCoboundary

/--
[kwf_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwffaceclose.lean)
-/
@[path]
private lemma kwf_status_eq :
-- imply
  (∀ {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a), Vc.edges.Nodup → (kwf_LinkingEven (Vc.edges.toFinset) ↔ ∀ (x : Site 2) (p : (hypercubicLattice 2).Walk x x), kwf_faceParity (fwr_faceInside Vc) p = false)) ∧ (¬ ∃ c : Site 2 → Bool, ∀ {u v : Site 2}, (hypercubicLattice 2).Adj u v → (s(u, v) ∈ jed_cutSet jcw_shiftFace ↔ c u ≠ c v)) := by
-- proof
  apply StatMech.Walls.kwf_status

/--
[kwf_adjacentSquares_walkParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwffaceclose.lean)
-/
@[path]
private lemma kwf_adjacentSquares_walkParity_eq :
-- imply
  walkParity (hypercubicLattice 2) ceo_shiftSquare.edges.toFinset kwf_rightSquare = true := by
-- proof
  apply StatMech.Walls.kwf_adjacentSquares_walkParity

/--
[kwf_latLinkingParity_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwffaceclose.lean)
-/
@[path]
private lemma kwf_latLinkingParity_false_eq :
-- imply
  ¬ kwf_LatLinkingParity := by
-- proof
  apply StatMech.Walls.kwf_latLinkingParity_false

/--
[kwf_latLinking_of_crossEdge_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwffaceclose.lean)
-/
@[path]
private lemma kwf_latLinking_of_crossEdge_bounds_eq
-- given
  (hreg : DualWalkBoundsRegion (hypercubicLattice 2) (hypercubicLattice 2) crossEdge) :
-- imply
  kwf_LatLinkingParity := by
-- proof
  apply StatMech.Walls.kwf_latLinking_of_crossEdge_bounds hreg

/--
[kwf_crossEdge_boundsRegion_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwffaceclose.lean)
-/
@[path]
private lemma kwf_crossEdge_boundsRegion_false_eq :
-- imply
  ¬ DualWalkBoundsRegion (hypercubicLattice 2) (hypercubicLattice 2) crossEdge := by
-- proof
  apply StatMech.Walls.kwf_crossEdge_boundsRegion_false


-- created on 2026-10-23
