import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.arrreroute
open Finset Set SimpleGraph StatMech StatMech.Walls


/--
[arr_offPatch_Ksupport_of_K'support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arrreroute.lean)
-/
@[path]
private lemma arr_offPatch_Ksupport_of_K'support_eq
  {K : Finset (Site 2)}
  {c f : Site 2}
-- given
  (hc : ¬ ats_faceHasCorner c f)
  (hf : f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support) :
-- imply
  f ∈ (faceBoundaryGraph (↑K : Set (Site 2))).support := by
-- proof
  apply StatMech.Walls.arr_offPatch_Ksupport_of_K'support hc hf

/--
[arr_offPatch_K'support_of_Ksupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arrreroute.lean)
-/
@[path]
private lemma arr_offPatch_K'support_of_Ksupport_eq
  {K : Finset (Site 2)}
  {c f : Site 2}
-- given
  (hc : ¬ ats_faceHasCorner c f)
  (hf : f ∈ (faceBoundaryGraph (↑K : Set (Site 2))).support) :
-- imply
  f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support := by
-- proof
  apply StatMech.Walls.arr_offPatch_K'support_of_Ksupport hc hf

/--
[arr_offPatch_reachableK_of_anchor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arrreroute.lean)
-/
@[path]
private lemma arr_offPatch_reachableK_of_anchor_eq
  {K : Finset (Site 2)}
  {c a₀ : Site 2}
  {f : Site 2}
-- given
  (hreachK : fbc_BoundaryReachable (↑K : Set (Site 2)))
  (ha₀ : a₀ ∈ (faceBoundaryGraph (↑K : Set (Site 2))).support)
  (hc : ¬ ats_faceHasCorner c f)
  (hf : f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support) :
-- imply
  (faceBoundaryGraph (↑K : Set (Site 2))).Reachable f a₀ := by
-- proof
  apply StatMech.Walls.arr_offPatch_reachableK_of_anchor hreachK ha₀ hc hf

/--
[arr_hookB_of_adjToOffPatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arrreroute.lean)
-/
@[path]
private lemma arr_hookB_of_adjToOffPatch_eq
  {K : Finset (Site 2)}
  {c a₀ f g : Site 2}
-- given
  (hA' : ∀ w : Site 2, ¬ ats_faceHasCorner c w → w ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support → (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable w a₀)
  (hgc : ¬ ats_faceHasCorner c g)
  (hadj : (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Adj f g) :
-- imply
  (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable f a₀ := by
-- proof
  apply StatMech.Walls.arr_hookB_of_adjToOffPatch hA' hgc hadj

/--
[arr_hookB_of_hasOffPatchNeighbour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arrreroute.lean)
-/
@[path]
private lemma arr_hookB_of_hasOffPatchNeighbour_eq
  {K : Finset (Site 2)}
  {c a₀ f : Site 2}
-- given
  (hA' : ∀ w : Site 2, ¬ ats_faceHasCorner c w → w ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support → (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable w a₀)
  (hhook : ∃ g : Site 2, ¬ ats_faceHasCorner c g ∧ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Adj f g) :
-- imply
  (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable f a₀ := by
-- proof
  apply StatMech.Walls.arr_hookB_of_hasOffPatchNeighbour hA' hhook

/--
[arr_hookB_of_reachOffPatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arrreroute.lean)
-/
@[path]
private lemma arr_hookB_of_reachOffPatch_eq
  {K : Finset (Site 2)}
  {c a₀ f : Site 2}
-- given
  (hA' : ∀ w : Site 2, ¬ ats_faceHasCorner c w → w ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support → (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable w a₀)
  (hhook : ∃ g : Site 2, ¬ ats_faceHasCorner c g ∧ g ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support ∧ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable f g) :
-- imply
  (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable f a₀ := by
-- proof
  apply StatMech.Walls.arr_hookB_of_reachOffPatch hA' hhook

/--
[arr_offPatch_reachableK'_of_reroute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arrreroute.lean)
-/
@[path]
private lemma arr_offPatch_reachableK'_of_reroute_eq
  {K : Finset (Site 2)}
  {c a₀ : Site 2}
-- given
  (hR : arr_ReRoute K c a₀) :
-- imply
  ∀ f : Site 2, ¬ ats_faceHasCorner c f → f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support → (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).Reachable f a₀ := by
-- proof
  apply StatMech.Walls.arr_offPatch_reachableK'_of_reroute hR

/--
[arr_boundaryReachable_of_reroute_hook](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arrreroute.lean)
-/
@[path]
private lemma arr_boundaryReachable_of_reroute_hook_eq
  {K : Finset (Site 2)}
  {c a₀ : Site 2}
-- given
  (hR : arr_ReRoute K c a₀)
  (hH : arr_Hook K c) :
-- imply
  fbc_BoundaryReachable (↑(insert c K) : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.arr_boundaryReachable_of_reroute_hook hR hH

/--
[arr_attachStep_of_reroute_hook](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arrreroute.lean)
-/
@[path]
private lemma arr_attachStep_of_reroute_hook_eq
-- given
  (h : ∀ (K : Finset (Site 2)) (c : Site 2), c ∉ K → IsConnectedCluster K → pc2_HoleFree (↑K : Set (Site 2)) → fbc_BoundaryReachable (↑K : Set (Site 2)) → IsConnectedCluster (insert c K) → pc2_HoleFree (↑(insert c K) : Set (Site 2)) → ∃ a₀ : Site 2, arr_ReRoute K c a₀ ∧ arr_Hook K c) :
-- imply
  fbc_AttachStep := by
-- proof
  apply StatMech.Walls.arr_attachStep_of_reroute_hook h

/--
[arr_reRoute_of_cycleDatum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arrreroute.lean)
-/
@[path]
private lemma arr_reRoute_of_cycleDatum_eq
  {K : Finset (Site 2)}
  {c a₀ : Site 2}
-- given
  (h : arr_ReRouteFromCycle K c a₀) :
-- imply
  arr_ReRoute K c a₀ := by
-- proof
  apply StatMech.Walls.arr_reRoute_of_cycleDatum h

/--
[arr_reRouteClause_of_avoidWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arrreroute.lean)
-/
@[path]
private lemma arr_reRouteClause_of_avoidWalk_eq
  {K : Finset (Site 2)}
  {c a₀ f : Site 2}
  {p : (faceBoundaryGraph (↑K : Set (Site 2))).Walk f a₀}
-- given
  (hp : ∀ w ∈ p.support, ¬ ats_faceHasCorner c w) :
-- imply
  ∃ q : (faceBoundaryGraph (↑K : Set (Site 2))).Walk f a₀, ∀ w ∈ q.support, ¬ ats_faceHasCorner c w := by
-- proof
  apply StatMech.Walls.arr_reRouteClause_of_avoidWalk p hp

/--
[arr_avoidWalk_of_induceReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arrreroute.lean)
-/
@[path]
private lemma arr_avoidWalk_of_induceReachable_eq
  {K : Finset (Site 2)}
  {c f a₀ : Site 2}
-- given
  (hf : f ∈ arr_offPatchSet c)
  (ha₀ : a₀ ∈ arr_offPatchSet c)
  (h : ((faceBoundaryGraph (↑K : Set (Site 2))).induce (arr_offPatchSet c)).Reachable ⟨f, hf⟩ ⟨a₀, ha₀⟩) :
-- imply
  ∃ p : (faceBoundaryGraph (↑K : Set (Site 2))).Walk f a₀, ∀ w ∈ p.support, ¬ ats_faceHasCorner c w := by
-- proof
  apply StatMech.Walls.arr_avoidWalk_of_induceReachable hf ha₀ h

/--
[arr_reRoute_of_induceReachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arrreroute.lean)
-/
@[path]
private lemma arr_reRoute_of_induceReachable_eq
  {K : Finset (Site 2)}
  {c a₀ : Site 2}
-- given
  (ha₀ : a₀ ∈ arr_offPatchSet c)
  (h : ∀ (f : Site 2) (hfc : f ∈ arr_offPatchSet c), f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support → ((faceBoundaryGraph (↑K : Set (Site 2))).induce (arr_offPatchSet c)).Reachable ⟨f, hfc⟩ ⟨a₀, ha₀⟩) :
-- imply
  arr_ReRoute K c a₀ := by
-- proof
  apply StatMech.Walls.arr_reRoute_of_induceReachable ha₀ h

/--
[arr_faithful_tromino](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arrreroute.lean)
-/
@[path]
private lemma arr_faithful_tromino_eq :
-- imply
  insert (![(0:ℤ), 1] : Site 2) ats_domino = pc2_tromino ∧ fbc_BoundaryReachable (↑pc2_tromino : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.arr_faithful_tromino

/--
[arr_insert_tromino_eq_square](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arrreroute.lean)
-/
@[path]
private lemma arr_insert_tromino_eq_square_eq :
-- imply
  insert (![(1:ℤ), 1] : Site 2) pc2_tromino = arr_square := by
-- proof
  apply StatMech.Walls.arr_insert_tromino_eq_square

/--
[arr_c_notMem_tromino](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arrreroute.lean)
-/
@[path]
private lemma arr_c_notMem_tromino_eq :
-- imply
  (![(1:ℤ), 1] : Site 2) ∉ pc2_tromino := by
-- proof
  apply StatMech.Walls.arr_c_notMem_tromino

/--
[arr_attach_square_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arrreroute.lean)
-/
@[path]
private lemma arr_attach_square_data_eq :
-- imply
  (![(1:ℤ), 1] : Site 2) ∉ pc2_tromino ∧ IsConnectedCluster pc2_tromino ∧ insert (![(1:ℤ), 1] : Site 2) pc2_tromino = arr_square := by
-- proof
  apply StatMech.Walls.arr_attach_square_data


-- created on 2026-10-23
