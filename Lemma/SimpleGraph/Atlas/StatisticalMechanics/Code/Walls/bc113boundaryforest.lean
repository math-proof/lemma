import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc113boundaryforest.Part6
open Set SimpleGraph Finset StatMech StatMech.Walls


/--
[bc113_exists_closer_neighbour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean)
-/
@[path]
private lemma bc113_exists_closer_neighbour_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {v b : V}
-- given
  (hr : G.Reachable v b)
  (hne : v ≠ b) :
-- imply
  ∃ u, G.Adj v u ∧ G.dist u b < G.dist v b := by
-- proof
  apply StatMech.Walls.bc113_exists_closer_neighbour G hr hne

/--
[bc113_toB_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean)
-/
@[path]
private lemma bc113_toB_witness_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {v : V}
-- given
  (B : V → Prop)
  (hreach : bc113_ReachesB G B) :
-- imply
  ∃ b, B b ∧ G.Reachable v b ∧ G.dist v b = bc113_toB G B v := by
-- proof
  apply StatMech.Walls.bc113_toB_witness G B hreach v

/--
[bc113_toB_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean)
-/
@[path]
private lemma bc113_toB_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {v b : V}
-- given
  (B : V → Prop)
  (hb : B b)
  (hr : G.Reachable v b) :
-- imply
  bc113_toB G B v ≤ G.dist v b := by
-- proof
  apply StatMech.Walls.bc113_toB_le G B hb hr

/--
[bc113_toB_eq_zero_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean)
-/
@[path]
private lemma bc113_toB_eq_zero_of_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {v : V}
-- given
  (B : V → Prop)
  (hv : B v) :
-- imply
  bc113_toB G B v = 0 := by
-- proof
  apply StatMech.Walls.bc113_toB_eq_zero_of_mem G B hv

/--
[bc113_toB_pos_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean)
-/
@[path]
private lemma bc113_toB_pos_of_not_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {v : V}
-- given
  (B : V → Prop)
  (hreach : bc113_ReachesB G B)
  (hv : ¬ B v) :
-- imply
  0 < bc113_toB G B v := by
-- proof
  apply StatMech.Walls.bc113_toB_pos_of_not_mem G B hreach hv

/--
[bc113_exists_parent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean)
-/
@[path]
private lemma bc113_exists_parent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {v : V}
-- given
  (B : V → Prop)
  (hreach : bc113_ReachesB G B)
  (hv : ¬ B v) :
-- imply
  ∃ u, G.Adj v u ∧ bc113_toB G B u < bc113_toB G B v := by
-- proof
  apply StatMech.Walls.bc113_exists_parent G B hreach hv

/--
[bc113_parent_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean)
-/
@[path]
private lemma bc113_parent_spec_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {v : V}
-- given
  (B : V → Prop)
  (hreach : bc113_ReachesB G B)
  (hv : ¬ B v) :
-- imply
  G.Adj v (bc113_parent G B hreach v) ∧ bc113_toB G B (bc113_parent G B hreach v) < bc113_toB G B v := by
-- proof
  apply StatMech.Walls.bc113_parent_spec G B hreach hv

/--
[bc113_bForest_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean)
-/
@[path]
private lemma bc113_bForest_adj_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {x y : V}
-- given
  (B : V → Prop)
  (hreach : bc113_ReachesB G B) :
-- imply
  (bc113_bForest G B hreach).Adj x y ↔ (∃ v, ¬ B v ∧ s(x, y) = s(v, bc113_parent G B hreach v)) ∧ x ≠ y := by
-- proof
  apply StatMech.Walls.bc113_bForest_adj G B hreach

/--
[bc113_bForest_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean)
-/
@[path]
private lemma bc113_bForest_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (B : V → Prop)
  (hreach : bc113_ReachesB G B) :
-- imply
  bc113_bForest G B hreach ≤ G := by
-- proof
  apply StatMech.Walls.bc113_bForest_le G B hreach

/--
[bc113_bForest_toB_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean)
-/
@[path]
private lemma bc113_bForest_toB_ne_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {x y : V}
-- given
  (B : V → Prop)
  (hreach : bc113_ReachesB G B)
  (hxy : (bc113_bForest G B hreach).Adj x y) :
-- imply
  bc113_toB G B x ≠ bc113_toB G B y := by
-- proof
  apply StatMech.Walls.bc113_bForest_toB_ne G B hreach hxy

/--
[bc113_bForest_down_is_parent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean)
-/
@[path]
private lemma bc113_bForest_down_is_parent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {x y : V}
-- given
  (B : V → Prop)
  (hreach : bc113_ReachesB G B)
  (hxy : (bc113_bForest G B hreach).Adj x y)
  (hlt : bc113_toB G B y < bc113_toB G B x) :
-- imply
  ¬ B x ∧ y = bc113_parent G B hreach x := by
-- proof
  apply StatMech.Walls.bc113_bForest_down_is_parent G B hreach hxy hlt

/--
[bc113_bForest_down_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean)
-/
@[path]
private lemma bc113_bForest_down_unique_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {x y₁ y₂ : V}
-- given
  (B : V → Prop)
  (hreach : bc113_ReachesB G B)
  (h₁ : (bc113_bForest G B hreach).Adj x y₁)
  (h₂ : (bc113_bForest G B hreach).Adj x y₂)
  (hlt₁ : bc113_toB G B y₁ < bc113_toB G B x)
  (hlt₂ : bc113_toB G B y₂ < bc113_toB G B x) :
-- imply
  y₁ = y₂ := by
-- proof
  apply StatMech.Walls.bc113_bForest_down_unique G B hreach h₁ h₂ hlt₁ hlt₂

/--
[bc113_bForest_adj_parent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean)
-/
@[path]
private lemma bc113_bForest_adj_parent_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {v : V}
-- given
  (B : V → Prop)
  (hreach : bc113_ReachesB G B)
  (hv : ¬ B v) :
-- imply
  (bc113_bForest G B hreach).Adj v (bc113_parent G B hreach v) := by
-- proof
  apply StatMech.Walls.bc113_bForest_adj_parent G B hreach hv

/--
[bc113_bForest_degree_pos_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean)
-/
@[path]
private lemma bc113_bForest_degree_pos_of_not_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel (bc113_bForest G B hreach).Adj]
  {v : V}
-- given
  (B : V → Prop)
  (hreach : bc113_ReachesB G B)
  (hv : ¬ B v) :
-- imply
  1 ≤ (bc113_bForest G B hreach).degree v := by
-- proof
  apply StatMech.Walls.bc113_bForest_degree_pos_of_not_mem G B hreach hv

/--
[bc113_leaf_is_tip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean)
-/
@[path]
private lemma bc113_leaf_is_tip_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel (bc113_bForest G B hreach).Adj]
  {v : V}
-- given
  (B : V → Prop)
  (hreach : bc113_ReachesB G B)
  (hv : ¬ B v)
  (hdeg : (bc113_bForest G B hreach).degree v = 1) :
-- imply
  ∀ u, (bc113_bForest G B hreach).Adj v u → u = bc113_parent G B hreach v := by
-- proof
  apply StatMech.Walls.bc113_leaf_is_tip G B hreach hv hdeg

/--
[bc113_bForest_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean)
-/
@[path]
private lemma bc113_bForest_acyclic_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (B : V → Prop)
  (hreach : bc113_ReachesB G B) :
-- imply
  (bc113_bForest G B hreach).IsAcyclic := by
-- proof
  apply StatMech.Walls.bc113_bForest_acyclic G B hreach

/--
[bc113_bForest_degree_ge_two_of_child](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean)
-/
@[path]
private lemma bc113_bForest_degree_ge_two_of_child_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel (bc113_bForest G B hreach).Adj]
  {v w : V}
-- given
  (B : V → Prop)
  (hreach : bc113_ReachesB G B)
  (hv : ¬ B v)
  (hadjw : (bc113_bForest G B hreach).Adj v w)
  (hltw : bc113_toB G B v < bc113_toB G B w) :
-- imply
  2 ≤ (bc113_bForest G B hreach).degree v := by
-- proof
  apply StatMech.Walls.bc113_bForest_degree_ge_two_of_child G B hreach hv hadjw hltw

/--
[bc113_bForest_leaves_on_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean)
-/
@[path]
private lemma bc113_bForest_leaves_on_boundary_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel (bc113_bForest G B hreach).Adj]
  {v : V}
-- given
  (B : V → Prop)
  (hreach : bc113_ReachesB G B)
  (hchild : bc113_HasChild G B hreach)
  (hdeg : (bc113_bForest G B hreach).degree v = 1) :
-- imply
  B v := by
-- proof
  apply StatMech.Walls.bc113_bForest_leaves_on_boundary G B hreach hchild hdeg

/--
[bc113_bForest_degree_pos_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean)
-/
@[path]
private lemma bc113_bForest_degree_pos_of_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel (bc113_bForest G B hreach).Adj]
  {b : V}
-- given
  (B : V → Prop)
  (hreach : bc113_ReachesB G B)
  (hbc : bc113_BoundaryHasChild G B hreach)
  (hb : B b) :
-- imply
  1 ≤ (bc113_bForest G B hreach).degree b := by
-- proof
  apply StatMech.Walls.bc113_bForest_degree_pos_of_mem G B hreach hbc hb

/--
[bc113_bForest_min_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean)
-/
@[path]
private lemma bc113_bForest_min_degree_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel (bc113_bForest G B hreach).Adj]
  {v : V}
-- given
  (B : V → Prop)
  (hreach : bc113_ReachesB G B)
  (hbc : bc113_BoundaryHasChild G B hreach) :
-- imply
  1 ≤ (bc113_bForest G B hreach).degree v := by
-- proof
  apply StatMech.Walls.bc113_bForest_min_degree G B hreach hbc v

/--
[bc113_boundaryAnchored_forest_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean)
-/
@[path]
private lemma bc113_boundaryAnchored_forest_exists_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
-- given
  (B : V → Prop)
  (hreach : bc113_ReachesB G B)
  (hchild : bc113_HasChild G B hreach)
  (hbc : bc113_BoundaryHasChild G B hreach) :
-- imply
  ∃ (F : SimpleGraph V) (_ : DecidableRel F.Adj), F ≤ G ∧ F.IsAcyclic ∧ (∀ v, 1 ≤ F.degree v) ∧ (∀ v, F.degree v = 1 → B v) := by
-- proof
  apply StatMech.Walls.bc113_boundaryAnchored_forest_exists G B hreach hchild hbc

/--
[bc113_maxPotential_has_no_child](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean)
-/
@[path]
private lemma bc113_maxPotential_has_no_child_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {v : V}
-- given
  (B : V → Prop)
  (hreach : bc113_ReachesB G B)
  (hv : ¬ B v)
  (hmax : ∀ w, bc113_toB G B w ≤ bc113_toB G B v) :
-- imply
  ¬ ∃ w, (bc113_bForest G B hreach).Adj v w ∧ bc113_toB G B v < bc113_toB G B w := by
-- proof
  apply StatMech.Walls.bc113_maxPotential_has_no_child G B hreach hv hmax

/--
[bc113_no_boundaryAnchored_on_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean)
-/
@[path]
private lemma bc113_no_boundaryAnchored_on_triangle_eq
  [Fintype V]
  [DecidableEq V] :
-- imply
  ¬ ∃ (F : SimpleGraph (Fin 3)) (_ : DecidableRel F.Adj), F ≤ (⊤ : SimpleGraph (Fin 3)) ∧ F.IsAcyclic ∧ (∀ v, 1 ≤ F.degree v) ∧ (∀ v, F.degree v = 1 → v = 0) := by
-- proof
  apply StatMech.Walls.bc113_no_boundaryAnchored_on_triangle

/--
[bc113_boundaryAnchored_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean)
-/
@[path]
private lemma bc113_boundaryAnchored_nonvacuous_eq
  [Fintype V]
  [DecidableEq V] :
-- imply
  ∃ (F : SimpleGraph (Fin 2)) (_ : DecidableRel F.Adj), F ≤ (⊤ : SimpleGraph (Fin 2)) ∧ F.IsAcyclic ∧ (∀ v, 1 ≤ F.degree v) ∧ (∀ v, F.degree v = 1 → (fun _ : Fin 2 => True) v) := by
-- proof
  apply StatMech.Walls.bc113_boundaryAnchored_nonvacuous

/--
[bc113_hub_degree_ge_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean)
-/
@[path]
private lemma bc113_hub_degree_ge_three_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel (bc113_bForest G B hreach).Adj]
  {v w₁ w₂ : V}
-- given
  (B : V → Prop)
  (hreach : bc113_ReachesB G B)
  (hv : ¬ B v)
  (ha₁ : (bc113_bForest G B hreach).Adj v w₁)
  (ha₂ : (bc113_bForest G B hreach).Adj v w₂)
  (hlt₁ : bc113_toB G B v < bc113_toB G B w₁)
  (hlt₂ : bc113_toB G B v < bc113_toB G B w₂)
  (hne : w₁ ≠ w₂) :
-- imply
  3 ≤ (bc113_bForest G B hreach).degree v := by
-- proof
  apply StatMech.Walls.bc113_hub_degree_ge_three G B hreach hv ha₁ ha₂ hlt₁ hlt₂ hne

/--
[bc113_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean)
-/
@[path]
private lemma bc113_status_eq
  [Fintype V]
  [DecidableEq V] :
-- imply
  (∀ (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B), (bc113_bForest G B hreach) ≤ G ∧ (bc113_bForest G B hreach).IsAcyclic) ∧ (∀ (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B), bc113_HasChild G B hreach → bc113_BoundaryHasChild G B hreach → ∃ (F : SimpleGraph V) (_ : DecidableRel F.Adj), F ≤ G ∧ F.IsAcyclic ∧ (∀ v, 1 ≤ F.degree v) ∧ (∀ v, F.degree v = 1 → B v)) ∧ (¬ ∃ (F : SimpleGraph (Fin 3)) (_ : DecidableRel F.Adj), F ≤ (⊤ : SimpleGraph (Fin 3)) ∧ F.IsAcyclic ∧ (∀ v, 1 ≤ F.degree v) ∧ (∀ v, F.degree v = 1 → v = 0)) := by
-- proof
  apply StatMech.Walls.bc113_status


-- created on 2026-10-23
