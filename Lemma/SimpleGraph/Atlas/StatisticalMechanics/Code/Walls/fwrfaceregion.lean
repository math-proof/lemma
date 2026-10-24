import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.fwrfaceregion
open Set SimpleGraph StatMech StatMech.Walls


/--
[fwr_sharedEdge_eq_crossEdge_horiz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fwrfaceregion.lean)
-/
@[path]
private lemma fwr_sharedEdge_eq_crossEdge_horiz_eq
  {x y : ℤ} :
-- imply
  sharedPrimalEdge (![x, y] : Site 2) (![x + 1, y] : Site 2) = rpc_crossEdge (![x + 1, y + 1] : Site 2) (![x + 2, y + 1] : Site 2) := by
-- proof
  apply StatMech.Walls.fwr_sharedEdge_eq_crossEdge_horiz x y

/--
[fwr_sharedEdge_eq_crossEdge_vert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fwrfaceregion.lean)
-/
@[path]
private lemma fwr_sharedEdge_eq_crossEdge_vert_eq
  {x y : ℤ} :
-- imply
  sharedPrimalEdge (![x, y] : Site 2) (![x, y + 1] : Site 2) = rpc_crossEdge (![x + 1, y + 1] : Site 2) (![x + 1, y + 2] : Site 2) := by
-- proof
  apply StatMech.Walls.fwr_sharedEdge_eq_crossEdge_vert x y

/--
[fwr_faceInside_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fwrfaceregion.lean)
-/
@[path]
private lemma fwr_faceInside_mk_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : ℤ} :
-- imply
  fwr_faceInside Vc (![x, y] : Site 2) ↔ ¬ Even (jec_rayCount (![x + 1, y + 1] : Site 2) Vc) := by
-- proof
  apply StatMech.Walls.fwr_faceInside_mk Vc x y

/--
[fwr_paritySwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fwrfaceregion.lean)
-/
@[path]
private lemma fwr_paritySwap_eq
-- given
  (P Q : Prop) :
-- imply
  ((¬ P) ↔ ¬ ¬ Q) ↔ ((¬ Q) ↔ ¬ ¬ P) := by
-- proof
  apply StatMech.Walls.fwr_paritySwap P Q

/--
[fwr_faceCutFlip_aux_h](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fwrfaceregion.lean)
-/
@[path]
private lemma fwr_faceCutFlip_aux_h_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {c' d' : Site 2}
-- given
  (hcd : (hypercubicLattice 2).Adj c' d') :
-- imply
  ((¬ Even (jec_rayCount c' Vc)) ↔ ¬ ¬ Even (jec_rayCount d' Vc)) ↔ Odd (Vc.edges.count (rpc_crossEdge c' d')) := by
-- proof
  apply StatMech.Walls.fwr_faceCutFlip_aux_h Vc hcd

/--
[fwr_faceCutFlip_aux_v](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fwrfaceregion.lean)
-/
@[path]
private lemma fwr_faceCutFlip_aux_v_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {c' d' : Site 2}
-- given
  (hcd : (hypercubicLattice 2).Adj c' d') :
-- imply
  ((¬ Even (jec_rayCount c' Vc)) ↔ ¬ ¬ Even (jec_rayCount d' Vc)) ↔ Odd (Vc.edges.count (rpc_crossEdge c' d')) := by
-- proof
  apply StatMech.Walls.fwr_faceCutFlip_aux_v Vc hcd

/--
[fwr_faceCutFlip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fwrfaceregion.lean)
-/
@[path]
private lemma fwr_faceCutFlip_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {c d : Site 2}
-- given
  (hcd : (hypercubicLattice 2).Adj c d) :
-- imply
  (fwr_faceInside Vc c ↔ ¬ fwr_faceInside Vc d) ↔ Odd (Vc.edges.count (sharedPrimalEdge c d)) := by
-- proof
  apply StatMech.Walls.fwr_faceCutFlip Vc hcd

/--
[fwr_faceCutMatch_of_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fwrfaceregion.lean)
-/
@[path]
private lemma fwr_faceCutMatch_of_nodup_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {c d : Site 2}
-- given
  (hnd : Vc.edges.Nodup)
  (hcd : (hypercubicLattice 2).Adj c d) :
-- imply
  (fwr_faceInside Vc c ↔ ¬ fwr_faceInside Vc d) ↔ sharedPrimalEdge c d ∈ Vc.edges := by
-- proof
  apply StatMech.Walls.fwr_faceCutMatch_of_nodup Vc hnd hcd

/--
[fwr_jedCutSet_match_of_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fwrfaceregion.lean)
-/
@[path]
private lemma fwr_jedCutSet_match_of_nodup_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {c d : Site 2}
-- given
  (hnd : Vc.edges.Nodup)
  (hcd : (hypercubicLattice 2).Adj c d) :
-- imply
  sharedPrimalEdge c d ∈ jed_cutSet (fwr_faceInside Vc) ↔ sharedPrimalEdge c d ∈ Vc.edges := by
-- proof
  apply StatMech.Walls.fwr_jedCutSet_match_of_nodup Vc hnd hcd

/--
[fwr_primalWalkBoundsFaceRegion_of_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fwrfaceregion.lean)
-/
@[path]
private lemma fwr_primalWalkBoundsFaceRegion_of_nodup_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {u v : Site 2}
-- given
  (hnd : Vc.edges.Nodup)
  (huv : (hypercubicLattice 2).Adj u v) :
-- imply
  s(u, v) ∈ Vc.edges ↔ s(u, v) ∈ jed_cutSet (fwr_faceInside Vc) := by
-- proof
  apply StatMech.Walls.fwr_primalWalkBoundsFaceRegion_of_nodup Vc hnd huv

/--
[fwr_primalWalkBoundsFaceRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fwrfaceregion.lean)
-/
@[path]
private lemma fwr_primalWalkBoundsFaceRegion_eq :
-- imply
  fwr_PrimalWalkBoundsFaceRegion := by
-- proof
  apply StatMech.Walls.fwr_primalWalkBoundsFaceRegion

/--
[fwr_shiftSquare_faces_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fwrfaceregion.lean)
-/
@[path]
private lemma fwr_shiftSquare_faces_adj_eq :
-- imply
  (hypercubicLattice 2).Adj (![0, 0] : Site 2) (![0, 1] : Site 2) := by
-- proof
  apply StatMech.Walls.fwr_shiftSquare_faces_adj

/--
[fwr_shiftSquare_shared](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fwrfaceregion.lean)
-/
@[path]
private lemma fwr_shiftSquare_shared_eq :
-- imply
  sharedPrimalEdge (![0, 0] : Site 2) (![0, 1] : Site 2) = s((![0, 1] : Site 2), (![1, 1] : Site 2)) := by
-- proof
  apply StatMech.Walls.fwr_shiftSquare_shared

/--
[fwr_shiftSquare_faceCut_works](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fwrfaceregion.lean)
-/
@[path]
private lemma fwr_shiftSquare_faceCut_works_eq :
-- imply
  (fwr_faceInside ceo_shiftSquare (![0, 0] : Site 2) ↔ ¬ fwr_faceInside ceo_shiftSquare (![0, 1] : Site 2)) := by
-- proof
  apply StatMech.Walls.fwr_shiftSquare_faceCut_works

/--
[fwr_shiftSquare_rayCounts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fwrfaceregion.lean)
-/
@[path]
private lemma fwr_shiftSquare_rayCounts_eq :
-- imply
  jec_rayCount (![1, 1] : Site 2) ceo_shiftSquare = 0 ∧ jec_rayCount (![1, 2] : Site 2) ceo_shiftSquare = 1 := by
-- proof
  apply StatMech.Walls.fwr_shiftSquare_rayCounts

/--
[fwr_shiftSquare_nonedge_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fwrfaceregion.lean)
-/
@[path]
private lemma fwr_shiftSquare_nonedge_left_eq :
-- imply
  s((![0, 0] : Site 2), (![0, 1] : Site 2)) ∉ ceo_shiftSquare.edges := by
-- proof
  apply StatMech.Walls.fwr_shiftSquare_nonedge_left

/--
[fwr_shiftSquare_nonedge_bottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fwrfaceregion.lean)
-/
@[path]
private lemma fwr_shiftSquare_nonedge_bottom_eq :
-- imply
  s((![0, 0] : Site 2), (![1, 0] : Site 2)) ∉ ceo_shiftSquare.edges := by
-- proof
  apply StatMech.Walls.fwr_shiftSquare_nonedge_bottom

/--
[fwr_shiftSquare_nonedge_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fwrfaceregion.lean)
-/
@[path]
private lemma fwr_shiftSquare_nonedge_right_eq :
-- imply
  s((![1, 0] : Site 2), (![1, 1] : Site 2)) ∉ ceo_shiftSquare.edges := by
-- proof
  apply StatMech.Walls.fwr_shiftSquare_nonedge_right

/--
[fwr_primalWalkBoundsRegion_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fwrfaceregion.lean)
-/
@[path]
private lemma fwr_primalWalkBoundsRegion_false_eq :
-- imply
  ¬ PrimalWalkBoundsRegion := by
-- proof
  apply StatMech.Walls.fwr_primalWalkBoundsRegion_false

/--
[fwr_faceCutMatch_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fwrfaceregion.lean)
-/
@[path]
private lemma fwr_faceCutMatch_nil_eq
  {a : Site 2}
  {c d : Site 2}
-- given
  (hcd : (hypercubicLattice 2).Adj c d) :
-- imply
  (fwr_faceInside (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk a a) c ↔ ¬ fwr_faceInside (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk a a) d) ↔ sharedPrimalEdge c d ∈ (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk a a).edges := by
-- proof
  apply StatMech.Walls.fwr_faceCutMatch_nil hcd

/--
[fwr_scope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fwrfaceregion.lean)
-/
@[path]
private lemma fwr_scope_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {c d : Site 2}
-- given
  (hcd : (hypercubicLattice 2).Adj c d) :
-- imply
  ((fwr_faceInside Vc c ↔ ¬ fwr_faceInside Vc d) ↔ Odd (Vc.edges.count (sharedPrimalEdge c d))) ∧ (Vc.edges.Nodup → ((fwr_faceInside Vc c ↔ ¬ fwr_faceInside Vc d) ↔ sharedPrimalEdge c d ∈ Vc.edges)) := by
-- proof
  apply StatMech.Walls.fwr_scope Vc hcd


-- created on 2026-10-23
