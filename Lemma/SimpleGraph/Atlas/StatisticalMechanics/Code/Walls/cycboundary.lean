import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.cycboundary
open Finset Set SimpleGraph StatMech StatMech.Walls


/--
[cyc_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/cycboundary.lean)
-/
@[path]
private lemma cyc_connected_eq
  {K : Set (Site 2)}
-- given
  (h : cyc_BoundaryCycle K) :
-- imply
  fbc_BoundaryReachable K := by
-- proof
  apply StatMech.Walls.cyc_connected h

/--
[cyc_degreeTwo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/cycboundary.lean)
-/
@[path]
private lemma cyc_degreeTwo_eq
  {K : Set (Site 2)}
  {f : Site 2}
-- given
  (h : cyc_BoundaryCycle K)
  (hf : f ∈ (faceBoundaryGraph K).support) :
-- imply
  (faceBoundaryGraph K).degree f = 2 := by
-- proof
  apply StatMech.Walls.cyc_degreeTwo h hf

/--
[cyc_boundaryCycle_imp_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/cycboundary.lean)
-/
@[path]
private lemma cyc_boundaryCycle_imp_reachable_eq
  {K : Set (Site 2)}
-- given
  (h : cyc_BoundaryCycle K) :
-- imply
  fbc_BoundaryReachable K := by
-- proof
  apply StatMech.Walls.cyc_boundaryCycle_imp_reachable h

/--
[cyc_degree_pos_of_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/cycboundary.lean)
-/
@[path]
private lemma cyc_degree_pos_of_support_eq
  {K : Set (Site 2)}
  {f : Site 2}
-- given
  (hf : f ∈ (faceBoundaryGraph K).support) :
-- imply
  0 < (faceBoundaryGraph K).degree f := by
-- proof
  apply StatMech.Walls.cyc_degree_pos_of_support hf

/--
[cyc_degree_ge_two_of_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/cycboundary.lean)
-/
@[path]
private lemma cyc_degree_ge_two_of_support_eq
  {K : Set (Site 2)}
  {f : Site 2}
-- given
  (hf : f ∈ (faceBoundaryGraph K).support) :
-- imply
  2 ≤ (faceBoundaryGraph K).degree f := by
-- proof
  apply StatMech.Walls.cyc_degree_ge_two_of_support hf

/--
[cyc_degree_two_iff_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/cycboundary.lean)
-/
@[path]
private lemma cyc_degree_two_iff_le_two_eq
  {K : Set (Site 2)}
  {f : Site 2}
-- given
  (hf : f ∈ (faceBoundaryGraph K).support) :
-- imply
  (faceBoundaryGraph K).degree f = 2 ↔ (faceBoundaryGraph K).degree f ≤ 2 := by
-- proof
  apply StatMech.Walls.cyc_degree_two_iff_le_two hf

/--
[cyc_boundaryCycle_of_noPinch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/cycboundary.lean)
-/
@[path]
private lemma cyc_boundaryCycle_of_noPinch_eq
  {K : Set (Site 2)}
-- given
  (hreach : fbc_BoundaryReachable K)
  (hnp : cyc_NoPinch K) :
-- imply
  cyc_BoundaryCycle K := by
-- proof
  apply StatMech.Walls.cyc_boundaryCycle_of_noPinch hreach hnp

/--
[cyc_singleton_face00_degree_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/cycboundary.lean)
-/
@[path]
private lemma cyc_singleton_face00_degree_two_eq :
-- imply
  (faceBoundaryGraph (↑({origin 2} : Finset (Site 2)) : Set (Site 2))).degree ![(0:ℤ), 0] = 2 := by
-- proof
  apply StatMech.Walls.cyc_singleton_face00_degree_two

/--
[cyc_pinch_face_degree_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/cycboundary.lean)
-/
@[path]
private lemma cyc_pinch_face_degree_four_eq :
-- imply
  (faceBoundaryGraph (↑cyc_pinch : Set (Site 2))).degree ![(0:ℤ), 0] = 4 := by
-- proof
  apply StatMech.Walls.cyc_pinch_face_degree_four

/--
[cyc_pinch_not_boundaryCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/cycboundary.lean)
-/
@[path]
private lemma cyc_pinch_not_boundaryCycle_eq :
-- imply
  ¬ cyc_BoundaryCycle (↑cyc_pinch : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.cyc_pinch_not_boundaryCycle

/--
[cyc_mem_support_iff_neighbor_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/cycboundary.lean)
-/
@[path]
private lemma cyc_mem_support_iff_neighbor_nonempty_eq
  {K : Set (Site 2)}
  {f : Site 2} :
-- imply
  f ∈ (faceBoundaryGraph K).support ↔ ((faceBoundaryGraph K).neighborSet f).Nonempty := by
-- proof
  apply StatMech.Walls.cyc_mem_support_iff_neighbor_nonempty

/--
[cyc_neighborSet_ncard_of_degree_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/cycboundary.lean)
-/
@[path]
private lemma cyc_neighborSet_ncard_of_degree_two_eq
  {K : Set (Site 2)}
  {f : Site 2}
-- given
  (h : (faceBoundaryGraph K).degree f = 2) :
-- imply
  ((faceBoundaryGraph K).neighborSet f).ncard = 2 := by
-- proof
  apply StatMech.Walls.cyc_neighborSet_ncard_of_degree_two h

/--
[cyc_isCycles_of_boundaryCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/cycboundary.lean)
-/
@[path]
private lemma cyc_isCycles_of_boundaryCycle_eq
  {K : Set (Site 2)}
-- given
  (h : cyc_BoundaryCycle K) :
-- imply
  (faceBoundaryGraph K).IsCycles := by
-- proof
  apply StatMech.Walls.cyc_isCycles_of_boundaryCycle h

/--
[cyc_degree_two_of_isCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/cycboundary.lean)
-/
@[path]
private lemma cyc_degree_two_of_isCycles_eq
  {K : Set (Site 2)}
  {f : Site 2}
-- given
  (h : (faceBoundaryGraph K).IsCycles)
  (hf : f ∈ (faceBoundaryGraph K).support) :
-- imply
  (faceBoundaryGraph K).degree f = 2 := by
-- proof
  apply StatMech.Walls.cyc_degree_two_of_isCycles h hf

/--
[cyc_boundaryCycle_of_isCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/cycboundary.lean)
-/
@[path]
private lemma cyc_boundaryCycle_of_isCycles_eq
  {K : Set (Site 2)}
-- given
  (hreach : fbc_BoundaryReachable K)
  (hcyc : (faceBoundaryGraph K).IsCycles) :
-- imply
  cyc_BoundaryCycle K := by
-- proof
  apply StatMech.Walls.cyc_boundaryCycle_of_isCycles hreach hcyc

/--
[cyc_reachable_deleteEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/cycboundary.lean)
-/
@[path]
private lemma cyc_reachable_deleteEdge_eq
  {K : Finset (Site 2)}
  {v w : Site 2}
-- given
  (hadj : (faceBoundaryGraph (↑K : Set (Site 2))).Adj v w) :
-- imply
  ((faceBoundaryGraph (↑K : Set (Site 2))).deleteEdges {s(v, w)}).Reachable v w := by
-- proof
  apply StatMech.Walls.cyc_reachable_deleteEdge hadj

/--
[cyc_attachReachable_of_preserves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/cycboundary.lean)
-/
@[path]
private lemma cyc_attachReachable_of_preserves_eq
  {K : Finset (Site 2)}
  {c : Site 2}
-- given
  (hpres : cyc_AttachPreservesCycle)
  (hc : c ∉ K)
  (hconn : IsConnectedCluster K)
  (hhf : pc2_HoleFree (↑K : Set (Site 2)))
  (hcyc : cyc_BoundaryCycle (↑K : Set (Site 2)))
  (hconn' : IsConnectedCluster (insert c K))
  (hhf' : pc2_HoleFree (↑(insert c K) : Set (Site 2))) :
-- imply
  fbc_BoundaryReachable (↑(insert c K) : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.cyc_attachReachable_of_preserves hpres K c hc hconn hhf hcyc hconn' hhf'

/--
[cyc_boundaryCycle_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/cycboundary.lean)
-/
@[path]
private lemma cyc_boundaryCycle_singleton_eq :
-- imply
  cyc_BoundaryCycle (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.cyc_boundaryCycle_singleton

/--
[cyc_boundaryCycle_of_inputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/cycboundary.lean)
-/
@[path]
private lemma cyc_boundaryCycle_of_inputs_eq
  {K : Finset (Site 2)}
-- given
  (hpres : cyc_AttachPreservesCycle)
  (hrem : fbc_HasRemovableCell)
  (hconn : IsConnectedCluster K)
  (hhf : pc2_HoleFree (↑K : Set (Site 2))) :
-- imply
  cyc_BoundaryCycle (↑K : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.cyc_boundaryCycle_of_inputs hpres hrem K hconn hhf

/--
[cyc_boundaryConnResidue_of_inputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/cycboundary.lean)
-/
@[path]
private lemma cyc_boundaryConnResidue_of_inputs_eq
-- given
  (hpres : cyc_AttachPreservesCycle)
  (hrem : fbc_HasRemovableCell) :
-- imply
  fbc_BoundaryConnResidue := by
-- proof
  apply StatMech.Walls.cyc_boundaryConnResidue_of_inputs hpres hrem

/--
[cyc_attachPreservesCycle_of_reachable_noPinch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/cycboundary.lean)
-/
@[path]
private lemma cyc_attachPreservesCycle_of_reachable_noPinch_eq
-- given
  (hI : ∀ (K : Finset (Site 2)) (c : Site 2), c ∉ K → IsConnectedCluster K → pc2_HoleFree (↑K : Set (Site 2)) → cyc_BoundaryCycle (↑K : Set (Site 2)) → IsConnectedCluster (insert c K) → pc2_HoleFree (↑(insert c K) : Set (Site 2)) → fbc_BoundaryReachable (↑(insert c K) : Set (Site 2)))
  (hII : ∀ (K : Finset (Site 2)) (c : Site 2), c ∉ K → IsConnectedCluster K → pc2_HoleFree (↑K : Set (Site 2)) → cyc_BoundaryCycle (↑K : Set (Site 2)) → IsConnectedCluster (insert c K) → pc2_HoleFree (↑(insert c K) : Set (Site 2)) → cyc_NoPinch (↑(insert c K) : Set (Site 2))) :
-- imply
  cyc_AttachPreservesCycle := by
-- proof
  apply StatMech.Walls.cyc_attachPreservesCycle_of_reachable_noPinch hI hII

/--
[cyc_reachable_of_arr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/cycboundary.lean)
-/
@[path]
private lemma cyc_reachable_of_arr_eq
  {K : Finset (Site 2)}
  {c a₀ : Site 2}
-- given
  (hR : arr_ReRoute K c a₀)
  (hH : arr_Hook K c) :
-- imply
  fbc_BoundaryReachable (↑(insert c K) : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.cyc_reachable_of_arr hR hH

/--
[cyc_reachable_of_arcReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/cycboundary.lean)
-/
@[path]
private lemma cyc_reachable_of_arcReachable_eq
  {K : Finset (Site 2)}
  {c a₀ : Site 2}
-- given
  (ha₀ : a₀ ∈ arr_offPatchSet c)
  (harc : ∀ (f : Site 2) (hfc : f ∈ arr_offPatchSet c), f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support → ((faceBoundaryGraph (↑K : Set (Site 2))).induce (arr_offPatchSet c)).Reachable ⟨f, hfc⟩ ⟨a₀, ha₀⟩)
  (hH : arr_Hook K c) :
-- imply
  fbc_BoundaryReachable (↑(insert c K) : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.cyc_reachable_of_arcReachable ha₀ harc hH


-- created on 2026-10-23
