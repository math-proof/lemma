import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.arccontiguity
open Finset Set SimpleGraph StatMech StatMech.Walls


/--
[arc_reachable_induce_of_avoidWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arccontiguity.lean)
-/
@[path]
private lemma arc_reachable_induce_of_avoidWalk_eq
  {G : SimpleGraph V}
  {S : Set V}
  {x y : V}
  {p : G.Walk x y}
-- given
  (hx : x ∈ S)
  (hy : y ∈ S)
  (hp : ∀ w ∈ p.support, w ∈ S) :
-- imply
  (G.induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
-- proof
  apply StatMech.Walls.arc_reachable_induce_of_avoidWalk hx hy p hp

/--
[arc_reachable_induce_compl_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arccontiguity.lean)
-/
@[path]
private lemma arc_reachable_induce_compl_singleton_eq
  {G : SimpleGraph V}
  [Empty.Finite V]
  {v a b : V}
-- given
  (hcyc : G.IsCycles)
  (hab : a ≠ b)
  (hva : G.Adj v a)
  (hvb : G.Adj v b)
  (ha : a ∈ ({v}ᶜ : Set V))
  (hb : b ∈ ({v}ᶜ : Set V)) :
-- imply
  (G.induce ({v}ᶜ : Set V)).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
-- proof
  apply StatMech.Walls.arc_reachable_induce_compl_singleton hcyc hab hva hvb ha hb

/--
[arc_reachable_induce_compl_pathInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arccontiguity.lean)
-/
@[path]
private lemma arc_reachable_induce_compl_pathInterior_eq
  {G : SimpleGraph V}
  [Empty.Finite V]
  {x y : V}
  {p : G.Walk x y}
-- given
  (hcyc : G.IsCycles)
  (hxy : x ≠ y)
  (hp : p.IsPath)
  (hx : x ∈ ({w | w ∈ p.support ∧ w ≠ x ∧ w ≠ y}ᶜ : Set V))
  (hy : y ∈ ({w | w ∈ p.support ∧ w ≠ x ∧ w ≠ y}ᶜ : Set V)) :
-- imply
  (G.induce ({w | w ∈ p.support ∧ w ≠ x ∧ w ≠ y}ᶜ : Set V)).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
-- proof
  apply StatMech.Walls.arc_reachable_induce_compl_pathInterior hcyc hxy p hp hx hy

/--
[arc_reachable_induce_mono_of_avoidWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arccontiguity.lean)
-/
@[path]
private lemma arc_reachable_induce_mono_of_avoidWalk_eq
  {G : SimpleGraph V}
  {S : Set V}
  {x y : V}
  {p : G.Walk x y}
-- given
  (hx : x ∈ S)
  (hy : y ∈ S)
  (hp : ∀ w ∈ p.support, w ∈ S) :
-- imply
  (G.induce S).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
-- proof
  apply StatMech.Walls.arc_reachable_induce_mono_of_avoidWalk hx hy p hp

/--
[arc_noncontig_can_disconnect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arccontiguity.lean)
-/
@[path]
private lemma arc_noncontig_can_disconnect_eq
  {K : Finset (Site 2)}
  {c a₀ : Site 2} :
-- imply
  ∃ (W : Type) (H : SimpleGraph W) (_ : H.IsCycles) (D : Set W) (a c : W) (ha : a ∈ Dᶜ) (hc : c ∈ Dᶜ), ¬ (H.induce (Dᶜ)).Reachable ⟨a, ha⟩ ⟨c, hc⟩ := by
-- proof
  apply StatMech.Walls.arc_noncontig_can_disconnect

/--
[arc_endpoints_reachable_offPatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arccontiguity.lean)
-/
@[path]
private lemma arc_endpoints_reachable_offPatch_eq
  {K : Finset (Site 2)}
  {c a₀ : Site 2}
  {x y : Site 2}
  {p : (faceBoundaryGraph (↑K : Set (Site 2))).Walk x y}
-- given
  (hcyc : cyc_BoundaryCycle (↑K : Set (Site 2)))
  (hxy : x ≠ y)
  (hp : p.IsPath)
  (hint : ∀ w ∈ p.support, w ≠ x → w ≠ y → ats_faceHasCorner c w)
  (hpatch : ∀ w : Site 2, ats_faceHasCorner c w → w ∈ (faceBoundaryGraph (↑K : Set (Site 2))).support → w ∈ p.support)
  (hx : x ∈ arr_offPatchSet c)
  (hy : y ∈ arr_offPatchSet c) :
-- imply
  ((faceBoundaryGraph (↑K : Set (Site 2))).induce (arr_offPatchSet c)).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
-- proof
  apply StatMech.Walls.arc_endpoints_reachable_offPatch hcyc hxy p hp hint hpatch hx hy

/--
[arc_harc_of_patchContiguous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arccontiguity.lean)
-/
@[path]
private lemma arc_harc_of_patchContiguous_eq
  {K : Finset (Site 2)}
  {c a₀ : Site 2}
-- given
  (hpc : arc_PatchContiguous K c a₀) :
-- imply
  ∀ (f : Site 2) (hfc : f ∈ arr_offPatchSet c), f ∈ (faceBoundaryGraph (↑(insert c K) : Set (Site 2))).support → ((faceBoundaryGraph (↑K : Set (Site 2))).induce (arr_offPatchSet c)).Reachable ⟨f, hfc⟩ ⟨a₀, hpc.1⟩ := by
-- proof
  apply StatMech.Walls.arc_harc_of_patchContiguous hpc

/--
[arc_cycleReachable_of_contiguous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arccontiguity.lean)
-/
@[path]
private lemma arc_cycleReachable_of_contiguous_eq
  {K : Finset (Site 2)}
  {c a₀ : Site 2}
-- given
  (hpc : arc_PatchContiguous K c a₀)
  (hH : arr_Hook K c) :
-- imply
  fbc_BoundaryReachable (↑(insert c K) : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.arc_cycleReachable_of_contiguous hpc hH

/--
[arc_attachPreservesCycle_of_contiguous_noPinch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arccontiguity.lean)
-/
@[path]
private lemma arc_attachPreservesCycle_of_contiguous_noPinch_eq
-- given
  (hAC : ∀ (K : Finset (Site 2)) (c : Site 2), c ∉ K → IsConnectedCluster K → pc2_HoleFree (↑K : Set (Site 2)) → cyc_BoundaryCycle (↑K : Set (Site 2)) → IsConnectedCluster (insert c K) → pc2_HoleFree (↑(insert c K) : Set (Site 2)) → ∃ a₀ : Site 2, arc_PatchContiguous K c a₀ ∧ arr_Hook K c)
  (hII : ∀ (K : Finset (Site 2)) (c : Site 2), c ∉ K → IsConnectedCluster K → pc2_HoleFree (↑K : Set (Site 2)) → cyc_BoundaryCycle (↑K : Set (Site 2)) → IsConnectedCluster (insert c K) → pc2_HoleFree (↑(insert c K) : Set (Site 2)) → cyc_NoPinch (↑(insert c K) : Set (Site 2))) :
-- imply
  cyc_AttachPreservesCycle := by
-- proof
  apply StatMech.Walls.arc_attachPreservesCycle_of_contiguous_noPinch hAC hII

/--
[arc_boundaryConnResidue_of_contiguous_noPinch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arccontiguity.lean)
-/
@[path]
private lemma arc_boundaryConnResidue_of_contiguous_noPinch_eq
-- given
  (hAC : ∀ (K : Finset (Site 2)) (c : Site 2), c ∉ K → IsConnectedCluster K → pc2_HoleFree (↑K : Set (Site 2)) → cyc_BoundaryCycle (↑K : Set (Site 2)) → IsConnectedCluster (insert c K) → pc2_HoleFree (↑(insert c K) : Set (Site 2)) → ∃ a₀ : Site 2, arc_PatchContiguous K c a₀ ∧ arr_Hook K c)
  (hII : ∀ (K : Finset (Site 2)) (c : Site 2), c ∉ K → IsConnectedCluster K → pc2_HoleFree (↑K : Set (Site 2)) → cyc_BoundaryCycle (↑K : Set (Site 2)) → IsConnectedCluster (insert c K) → pc2_HoleFree (↑(insert c K) : Set (Site 2)) → cyc_NoPinch (↑(insert c K) : Set (Site 2)))
  (hrem : fbc_HasRemovableCell) :
-- imply
  fbc_BoundaryConnResidue := by
-- proof
  apply StatMech.Walls.arc_boundaryConnResidue_of_contiguous_noPinch hAC hII hrem

/--
[arc_contig_singleton_stays_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arccontiguity.lean)
-/
@[path]
private lemma arc_contig_singleton_stays_connected_eq :
-- imply
  ∃ (ha : (0 : Fin 4) ∈ ({(1 : Fin 4)}ᶜ : Set (Fin 4))) (hb : (2 : Fin 4) ∈ ({(1 : Fin 4)}ᶜ : Set (Fin 4))), ((cycleGraph 4).induce ({(1 : Fin 4)}ᶜ : Set (Fin 4))).Reachable ⟨0, ha⟩ ⟨2, hb⟩ := by
-- proof
  apply StatMech.Walls.arc_contig_singleton_stays_connected

/--
[arc_faithful_tromino](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/arccontiguity.lean)
-/
@[path]
private lemma arc_faithful_tromino_eq :
-- imply
  insert (![(0:ℤ), 1] : Site 2) ats_domino = pc2_tromino ∧ fbc_BoundaryReachable (↑pc2_tromino : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.arc_faithful_tromino


-- created on 2026-10-23
