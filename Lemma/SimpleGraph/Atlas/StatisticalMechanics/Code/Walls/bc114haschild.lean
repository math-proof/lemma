import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc114haschild
open Set SimpleGraph Finset StatMech StatMech.Walls


/--
[bc114_internal_two_neighbours](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc114haschild.lean)
-/
@[path]
private lemma bc114_internal_two_neighbours_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {F : SimpleGraph V}
  {s t : V}
  {p : F.Walk s t}
  {i : ℕ}
-- given
  (hp : p.IsPath)
  (hi0 : 0 < i)
  (hilt : i < p.length) :
-- imply
  F.Adj (p.getVert i) (p.getVert (i - 1)) ∧ F.Adj (p.getVert i) (p.getVert (i + 1)) ∧ p.getVert (i - 1) ≠ p.getVert (i + 1) := by
-- proof
  apply StatMech.Walls.bc114_internal_two_neighbours F p hp hi0 hilt

/--
[bc114_internal_degree_ge_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc114haschild.lean)
-/
@[path]
private lemma bc114_internal_degree_ge_two_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {F : SimpleGraph V}
  [DecidableRel F.Adj]
  {s t : V}
  {p : F.Walk s t}
  {i : ℕ}
-- given
  (hp : p.IsPath)
  (hi0 : 0 < i)
  (hilt : i < p.length) :
-- imply
  2 ≤ F.degree (p.getVert i) := by
-- proof
  apply StatMech.Walls.bc114_internal_degree_ge_two F p hp hi0 hilt

/--
[bc114_isInternal_degree_ge_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc114haschild.lean)
-/
@[path]
private lemma bc114_isInternal_degree_ge_two_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {F : SimpleGraph V}
  [DecidableRel F.Adj]
  {v : V}
-- given
  (hv : bc114_IsInternal F v) :
-- imply
  2 ≤ F.degree v := by
-- proof
  apply StatMech.Walls.bc114_isInternal_degree_ge_two F hv

/--
[bc114_leaf_not_internal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc114haschild.lean)
-/
@[path]
private lemma bc114_leaf_not_internal_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {F : SimpleGraph V}
  [DecidableRel F.Adj]
  {v : V}
-- given
  (hdeg : F.degree v = 1) :
-- imply
  ¬ bc114_IsInternal F v := by
-- proof
  apply StatMech.Walls.bc114_leaf_not_internal F hdeg

/--
[bc114_leaf_on_boundary_of_armCovered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc114haschild.lean)
-/
@[path]
private lemma bc114_leaf_on_boundary_of_armCovered_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {F : SimpleGraph V}
  [DecidableRel F.Adj]
  {B H : V → Prop}
  {v : V}
-- given
  (hcov : bc114_ArmCovered F B H)
  (hhub : ∀ v, H v → 3 ≤ F.degree v)
  (hdeg : F.degree v = 1) :
-- imply
  B v := by
-- proof
  apply StatMech.Walls.bc114_leaf_on_boundary_of_armCovered F hcov hhub hdeg

/--
[bc114_isInternal_of_mem_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc114haschild.lean)
-/
@[path]
private lemma bc114_isInternal_of_mem_support_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {F : SimpleGraph V}
  {s t : V}
  {p : F.Walk s t}
  {v : V}
-- given
  (hp : p.IsPath)
  (hv : v ∈ p.support)
  (hvs : v ≠ s)
  (hvt : v ≠ t) :
-- imply
  bc114_IsInternal F v := by
-- proof
  apply StatMech.Walls.bc114_isInternal_of_mem_support F p hp hv hvs hvt

/--
[bc114_internal_of_reachable_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc114haschild.lean)
-/
@[path]
private lemma bc114_internal_of_reachable_boundary_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {F : SimpleGraph V}
  {a z : V}
  {v : V}
-- given
  (hr : F.Reachable a z)
  (hva : v ≠ a)
  (hvz : v ≠ z)
  (hmem : ∃ p : F.Walk a z, p.IsPath ∧ v ∈ p.support) :
-- imply
  bc114_IsInternal F v := by
-- proof
  apply StatMech.Walls.bc114_internal_of_reachable_boundary F hr hva hvz hmem

/--
[bc114_hasChild_of_forestNeighbour_up](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc114haschild.lean)
-/
@[path]
private lemma bc114_hasChild_of_forestNeighbour_up_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {G : SimpleGraph V}
-- given
  (B : V → Prop)
  (hreach : bc113_ReachesB G B)
  (hup : ∀ v, ¬ B v → ∃ w, (bc113_bForest G B hreach).Adj v w ∧ bc113_toB G B v < bc113_toB G B w) :
-- imply
  bc113_HasChild G B hreach := by
-- proof
  apply StatMech.Walls.bc114_hasChild_of_forestNeighbour_up G B hreach hup

/--
[bc114_bForest_internal_has_child](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc114haschild.lean)
-/
@[path]
private lemma bc114_bForest_internal_has_child_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {G : SimpleGraph V}
  [DecidableRel (bc113_bForest G B hreach).Adj]
  {v : V}
-- given
  (B : V → Prop)
  (hreach : bc113_ReachesB G B)
  (hv : ¬ B v)
  (hint : bc114_IsInternal (bc113_bForest G B hreach) v) :
-- imply
  ∃ w, (bc113_bForest G B hreach).Adj v w ∧ bc113_toB G B v < bc113_toB G B w := by
-- proof
  apply StatMech.Walls.bc114_bForest_internal_has_child G B hreach hv hint

/--
[bc114_hasChild_of_armCovered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc114haschild.lean)
-/
@[path]
private lemma bc114_hasChild_of_armCovered_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {G : SimpleGraph V}
  [DecidableRel (bc113_bForest G B hreach).Adj]
-- given
  (B : V → Prop)
  (hreach : bc113_ReachesB G B)
  (hcov : ∀ v, ¬ B v → bc114_IsInternal (bc113_bForest G B hreach) v) :
-- imply
  bc113_HasChild G B hreach := by
-- proof
  apply StatMech.Walls.bc114_hasChild_of_armCovered G B hreach hcov

/--
[bc114_armForest_boundaryAnchored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc114haschild.lean)
-/
@[path]
private lemma bc114_armForest_boundaryAnchored_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {F : SimpleGraph V}
  [DecidableRel F.Adj]
  {B H : V → Prop}
-- given
  (hcov : bc114_ArmCovered F B H)
  (hhub : ∀ v, H v → 3 ≤ F.degree v)
  (hac : F.IsAcyclic)
  (hmin : ∀ v, 1 ≤ F.degree v) :
-- imply
  F.IsAcyclic ∧ (∀ v, 1 ≤ F.degree v) ∧ (∀ v, F.degree v = 1 → B v) := by
-- proof
  apply StatMech.Walls.bc114_armForest_boundaryAnchored F hcov hhub hac hmin

/--
[bc114_obstruction_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc114haschild.lean)
-/
@[path]
private lemma bc114_obstruction_real_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V} :
-- imply
  ¬ ∃ (F : SimpleGraph (Fin 3)) (_ : DecidableRel F.Adj), F ≤ (⊤ : SimpleGraph (Fin 3)) ∧ F.IsAcyclic ∧ (∀ v, 1 ≤ F.degree v) ∧ (∀ v, F.degree v = 1 → v = 0) := by
-- proof
  apply StatMech.Walls.bc114_obstruction_real

/--
[bc114_leaf_not_armCovered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc114haschild.lean)
-/
@[path]
private lemma bc114_leaf_not_armCovered_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {F : SimpleGraph V}
  [DecidableRel F.Adj]
  {v : V}
-- given
  (hdeg : F.degree v = 1) :
-- imply
  ¬ bc114_IsInternal F v := by
-- proof
  apply StatMech.Walls.bc114_leaf_not_armCovered F hdeg

/--
[bc114_armCovered_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc114haschild.lean)
-/
@[path]
private lemma bc114_armCovered_nonvacuous_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V} :
-- imply
  bc114_IsInternal (SimpleGraph.fromEdgeSet {s((0 : Fin 3), 1), s((1 : Fin 3), 2)}) 1 := by
-- proof
  apply StatMech.Walls.bc114_armCovered_nonvacuous

/--
[bc114_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc114haschild.lean)
-/
@[path]
private lemma bc114_status_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V} :
-- imply
  (¬ ∃ (F : SimpleGraph (Fin 3)) (_ : DecidableRel F.Adj), F ≤ (⊤ : SimpleGraph (Fin 3)) ∧ F.IsAcyclic ∧ (∀ v, 1 ≤ F.degree v) ∧ (∀ v, F.degree v = 1 → v = 0)) ∧ (∀ (F : SimpleGraph V) [DecidableRel F.Adj] (B H : V → Prop), bc114_ArmCovered F B H → (∀ v, H v → 3 ≤ F.degree v) → ∀ v, F.degree v = 1 → B v) ∧ (∀ (F : SimpleGraph V) [DecidableRel F.Adj] (B H : V → Prop), bc114_ArmCovered F B H → (∀ v, H v → 3 ≤ F.degree v) → F.IsAcyclic → (∀ v, 1 ≤ F.degree v) → F.IsAcyclic ∧ (∀ v, 1 ≤ F.degree v) ∧ (∀ v, F.degree v = 1 → B v)) ∧ (∀ (F : SimpleGraph V) [DecidableRel F.Adj] (v : V), F.degree v = 1 → ¬ bc114_IsInternal F v) := by
-- proof
  apply StatMech.Walls.bc114_status


-- created on 2026-10-23
