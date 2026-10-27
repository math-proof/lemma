import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.fbcconnected.Part4
open Finset Set SimpleGraph StatMech StatMech.Walls


/--
[fbc_connected_of_common_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fbcconnected.lean)
-/
@[path]
private lemma fbc_connected_of_common_reach_eq
  {K : Set (Site 2)}
  {T : Finset (Site 2)}
  {a₀ : Site 2}
-- given
  (ha₀ : a₀ ∈ T)
  (hwalk : ∀ f ∈ T, ∃ p : (faceBoundaryGraph K).Walk a₀ f, ∀ v ∈ p.support, v ∈ T) :
-- imply
  FaceBoundaryConnected K T := by
-- proof
  apply StatMech.Walls.fbc_connected_of_common_reach ha₀ hwalk

/--
[fbc_connected_of_pairwise_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fbcconnected.lean)
-/
@[path]
private lemma fbc_connected_of_pairwise_reach_eq
  {K : Set (Site 2)}
  {T : Finset (Site 2)}
-- given
  (hne : T.Nonempty)
  (hwalk : ∀ f ∈ T, ∀ g ∈ T, ∃ p : (faceBoundaryGraph K).Walk f g, ∀ v ∈ p.support, v ∈ T) :
-- imply
  FaceBoundaryConnected K T := by
-- proof
  apply StatMech.Walls.fbc_connected_of_pairwise_reach hne hwalk

/--
[fbc_walk_support_in_boundarySupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fbcconnected.lean)
-/
@[path]
private lemma fbc_walk_support_in_boundarySupport_eq
  {K : Set (Site 2)}
  {f g : Site 2}
  {p : (faceBoundaryGraph K).Walk f g}
  {v : Site 2}
-- given
  (hK : K.Finite)
  (hf : f ∈ (boundarySupport hK : Set (Site 2)))
  (hg : g ∈ (boundarySupport hK : Set (Site 2)))
  (hv : v ∈ p.support) :
-- imply
  v ∈ boundarySupport hK := by
-- proof
  apply StatMech.Walls.fbc_walk_support_in_boundarySupport hK p hf hg v hv

/--
[fbc_connected_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fbcconnected.lean)
-/
@[path]
private lemma fbc_connected_of_reachable_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hne : (boundarySupport hK).Nonempty)
  (hreach : ∀ f ∈ (boundarySupport hK : Set (Site 2)), ∀ g ∈ (boundarySupport hK : Set (Site 2)), (faceBoundaryGraph K).Reachable f g) :
-- imply
  FaceBoundaryConnected K (boundarySupport hK) := by
-- proof
  apply StatMech.Walls.fbc_connected_of_reachable hK hne hreach

/--
[fbc_boundaryReachable_of_faceBoundaryConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fbcconnected.lean)
-/
@[path]
private lemma fbc_boundaryReachable_of_faceBoundaryConnected_eq
  {K : Set (Site 2)}
  {T : Finset (Site 2)}
-- given
  (hsupp : (faceBoundaryGraph K).support ⊆ (T : Set (Site 2)))
  (hconn : FaceBoundaryConnected K T) :
-- imply
  fbc_BoundaryReachable K := by
-- proof
  apply StatMech.Walls.fbc_boundaryReachable_of_faceBoundaryConnected hsupp hconn

/--
[fbc_support_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fbcconnected.lean)
-/
@[path]
private lemma fbc_support_nonempty_eq
  {K : Finset (Site 2)}
-- given
  (hne : K.Nonempty) :
-- imply
  ((faceBoundaryGraph (↑K : Set (Site 2))).support).Nonempty := by
-- proof
  apply StatMech.Walls.fbc_support_nonempty hne

/--
[fbc_faceBoundaryConnected_false_of_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fbcconnected.lean)
-/
@[path]
private lemma fbc_faceBoundaryConnected_false_of_isolated_eq
  {K : Set (Site 2)}
  {T : Finset (Site 2)}
  {w : Site 2}
  {s : Site 2}
-- given
  (hwT : w ∈ T)
  (hiso : w ∉ (faceBoundaryGraph K).support)
  (hsT : s ∈ T)
  (hs : s ∈ (faceBoundaryGraph K).support)
  (hws : w ≠ s) :
-- imply
  ¬ FaceBoundaryConnected K T := by
-- proof
  apply StatMech.Walls.fbc_faceBoundaryConnected_false_of_isolated hwT hiso hsT hs hws

/--
[fbc_boundaryReachable_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fbcconnected.lean)
-/
@[path]
private lemma fbc_boundaryReachable_singleton_eq :
-- imply
  fbc_BoundaryReachable (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.fbc_boundaryReachable_singleton

/--
[fbc_card_one_eq_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fbcconnected.lean)
-/
@[path]
private lemma fbc_card_one_eq_singleton_eq
  {K : Finset (Site 2)}
-- given
  (hconn : IsConnectedCluster K)
  (hcard : K.card = 1) :
-- imply
  K = {origin 2} := by
-- proof
  apply StatMech.Walls.fbc_card_one_eq_singleton hconn hcard

/--
[fbc_boundaryReachable_of_inputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fbcconnected.lean)
-/
@[path]
private lemma fbc_boundaryReachable_of_inputs_eq
  {K : Finset (Site 2)}
-- given
  (hattach : fbc_AttachStep)
  (hrem : fbc_HasRemovableCell)
  (hconn : IsConnectedCluster K)
  (hhf : pc2_HoleFree (↑K : Set (Site 2))) :
-- imply
  fbc_BoundaryReachable (↑K : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.fbc_boundaryReachable_of_inputs hattach hrem K hconn hhf

/--
[fbc_residue_of_inputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fbcconnected.lean)
-/
@[path]
private lemma fbc_residue_of_inputs_eq
-- given
  (hattach : fbc_AttachStep)
  (hrem : fbc_HasRemovableCell) :
-- imply
  fbc_BoundaryConnResidue := by
-- proof
  apply StatMech.Walls.fbc_residue_of_inputs hattach hrem

/--
[fbc_mem_tightSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fbcconnected.lean)
-/
@[path]
private lemma fbc_mem_tightSupport_eq
  {K : Set (Site 2)}
  {f : Site 2}
-- given
  (hK : K.Finite) :
-- imply
  f ∈ fbc_tightSupport hK ↔ f ∈ (faceBoundaryGraph K).support := by
-- proof
  apply StatMech.Walls.fbc_mem_tightSupport hK

/--
[fbc_tightSupport_covers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fbcconnected.lean)
-/
@[path]
private lemma fbc_tightSupport_covers_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite) :
-- imply
  (faceBoundaryGraph K).support ⊆ (fbc_tightSupport hK : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.fbc_tightSupport_covers hK

/--
[fbc_faceBoundaryConnected_tight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fbcconnected.lean)
-/
@[path]
private lemma fbc_faceBoundaryConnected_tight_eq
  {K : Finset (Site 2)}
-- given
  (hne : K.Nonempty)
  (hfin : (↑K : Set (Site 2)).Finite)
  (hreach : fbc_BoundaryReachable (↑K : Set (Site 2))) :
-- imply
  FaceBoundaryConnected (↑K : Set (Site 2)) (fbc_tightSupport hfin) := by
-- proof
  apply StatMech.Walls.fbc_faceBoundaryConnected_tight hne hfin hreach

/--
[fbc_single_dualCircuit_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fbcconnected.lean)
-/
@[path]
private lemma fbc_single_dualCircuit_of_residue_eq
  {K : Finset (Site 2)}
  {f₀ : Site 2}
-- given
  (h : fbc_BoundaryConnResidue)
  (hconn : IsConnectedCluster K)
  (hhf : pc2_HoleFree (↑K : Set (Site 2)))
  (hfin : (↑K : Set (Site 2)).Finite)
  (hf₀ : f₀ ∈ (fbc_tightSupport hfin : Set (Site 2))) :
-- imply
  ∃ c : (faceBoundaryGraph (↑K : Set (Site 2))).Walk f₀ f₀, c.IsTrail ∧ ∀ e ∈ (faceBoundaryGraph (↑K : Set (Site 2))).edgeSet, e ∈ c.edges := by
-- proof
  apply StatMech.Walls.fbc_single_dualCircuit_of_residue h K hconn hhf hfin hf₀

/--
[fbc_boundaryReachable_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fbcconnected.lean)
-/
@[path]
private lemma fbc_boundaryReachable_box_eq
  {m n : ℕ} :
-- imply
  fbc_BoundaryReachable (↑(boxCluster m n) : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.fbc_boundaryReachable_box m n

/--
[fbc_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/fbcconnected.lean)
-/
@[path]
private lemma fbc_nonvacuous_eq :
-- imply
  fbc_BoundaryReachable (↑({origin 2} : Finset (Site 2)) : Set (Site 2)) ∧ ∀ m n : ℕ, fbc_BoundaryReachable (↑(boxCluster m n) : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.fbc_nonvacuous


-- created on 2026-10-23
