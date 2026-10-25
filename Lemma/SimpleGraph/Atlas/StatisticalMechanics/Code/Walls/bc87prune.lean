import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc87prune
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc87_arm_reaches_outside_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc87prune.lean)
-/
@[path]
private lemma bc87_arm_reaches_outside_box_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y a : Site d}
  {n : ℕ}
-- given
  (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
-- imply
  ∃ z, z ∉ box d n ∧ Connected d (removeSites (bc61_boxAround d L y) ω) a z := by
-- proof
  apply StatMech.Walls.bc87_arm_reaches_outside_box ω L y a hinf n

/--
[bc87_coarseTrif_arms_reach_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc87prune.lean)
-/
@[path]
private lemma bc87_coarseTrif_arms_reach_outside_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d}
  {n : ℕ}
-- given
  (h : bc61_IsCoarseTrifurcation ω L y) :
-- imply
  ∃ a₁ a₂ a₃ : Site d, (∃ z, z ∉ box d n ∧ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ z) ∧ (∃ z, z ∉ box d n ∧ Connected d (removeSites (bc61_boxAround d L y) ω) a₂ z) ∧ (∃ z, z ∉ box d n ∧ Connected d (removeSites (bc61_boxAround d L y) ω) a₃ z) := by
-- proof
  apply StatMech.Walls.bc87_coarseTrif_arms_reach_outside ω L h n

/--
[bc87_pruning_preserves_branch_le_leaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc87prune.lean)
-/
@[path]
private lemma bc87_pruning_preserves_branch_le_leaf_eq
  {d : ℕ}
  {R : ℕ}
  {S : Set (Site d)}
  [Fintype (↑S : Type)]
  [Nonempty (↑S : Type)]
  {G : SimpleGraph (↑S : Type)}
  [DecidableRel G.Adj]
-- given
  (hacyc : G.IsAcyclic)
  (hmin : ∀ v : (↑S : Type), 1 ≤ G.degree v)
  (hbdry : ∀ v : (↑S : Type), G.degree v = 1 → (v : Site d) ∈ vertexBoundary d R) :
-- imply
  (univ.filter (fun v : (↑S : Type) => 3 ≤ G.degree v)).card ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc87_pruning_preserves_branch_le_leaf R G hacyc hmin hbdry

/--
[bc87_leaves_on_boundary_free_of_boundaryLeafClause](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc87prune.lean)
-/
@[path]
private lemma bc87_leaves_on_boundary_free_of_boundaryLeafClause_eq
  {d : ℕ}
  {R : ℕ}
  {S : Set (Site d)}
  [Fintype (↑S : Type)]
  {G : SimpleGraph (↑S : Type)}
  [DecidableRel G.Adj]
-- given
  (hbdry : ∀ v : (↑S : Type), G.degree v = 1 → (v : Site d) ∈ vertexBoundary d R) :
-- imply
  (univ.filter (fun v : (↑S : Type) => G.degree v = 1)).card ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc87_leaves_on_boundary_free_of_boundaryLeafClause R G hbdry

/--
[bc87_prune_step_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc87prune.lean)
-/
@[path]
private lemma bc87_prune_step_acyclic_eq
  {d : ℕ}
  {G : SimpleGraph V}
  {s : Set (Sym2 V)}
-- given
  (hacyc : G.IsAcyclic) :
-- imply
  (G.deleteEdges s).IsAcyclic := by
-- proof
  apply StatMech.Walls.bc87_prune_step_acyclic G hacyc s

/--
[bc87_prune_step_degree_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc87prune.lean)
-/
@[path]
private lemma bc87_prune_step_degree_le_eq
  {d : ℕ}
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : Set (Sym2 V)}
  [DecidableRel (G.deleteEdges s).Adj]
  {v : V} :
-- imply
  (G.deleteEdges s).degree v ≤ G.degree v := by
-- proof
  apply StatMech.Walls.bc87_prune_step_degree_le G s v

/--
[bc87_leaf_boundary_fully_perConfig_given_forest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc87prune.lean)
-/
@[path]
private lemma bc87_leaf_boundary_fully_perConfig_given_forest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
-- given
  (h : bc75_FiberGnTrifData ω L R c) :
-- imply
  (bc73_fiber ω L R c).card ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc87_leaf_boundary_fully_perConfig_given_forest ω L R c h

/--
[bc87_prune_reduces_to_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc87prune.lean)
-/
@[path]
private lemma bc87_prune_reduces_to_cut_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y y' : Site d}
-- given
  (hN : numInfiniteClusters d ω ≤ 1)
  (h : bc61_IsCoarseTrifurcation ω L y)
  (h' : bc61_IsCoarseTrifurcation ω L y') :
-- imply
  ∃ a a' : Site d, (cluster d ω a).Infinite ∧ (cluster d ω a').Infinite ∧ Connected d ω a a' := by
-- proof
  apply StatMech.Walls.bc87_prune_reduces_to_cut ω L hN h h'

/--
[bc87_witness_upperLines_arms_reach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc87prune.lean)
-/
@[path]
private lemma bc87_witness_upperLines_arms_reach_eq
  {d : ℕ}
  {L : ℕ}
  {n : ℕ}
-- given
  (hL : 3 ≤ L) :
-- imply
  ∃ a₁ a₂ a₃ : Site 2, (∃ z, z ∉ box 2 n ∧ Connected 2 (removeSites (bc61_boxAround 2 L (0 : Site 2)) bc60_upperLines) a₁ z) ∧ (∃ z, z ∉ box 2 n ∧ Connected 2 (removeSites (bc61_boxAround 2 L (0 : Site 2)) bc60_upperLines) a₂ z) ∧ (∃ z, z ∉ box 2 n ∧ Connected 2 (removeSites (bc61_boxAround 2 L (0 : Site 2)) bc60_upperLines) a₃ z) := by
-- proof
  apply StatMech.Walls.bc87_witness_upperLines_arms_reach hL n

/--
[bc87_witness_upperLines_N_top_cut_fails](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc87prune.lean)
-/
@[path]
private lemma bc87_witness_upperLines_N_top_cut_fails_eq
  {d : ℕ}
  {L : ℕ} :
-- imply
  numInfiniteClusters 2 bc60_upperLines = ⊤ ∧ (Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧ Connected 2 bc60_upperLines (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1)) := by
-- proof
  apply StatMech.Walls.bc87_witness_upperLines_N_top_cut_fails L

/--
[bc87_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc87prune.lean)
-/
@[path]
private lemma bc87_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (y : Site 2), bc61_IsCoarseTrifurcation ω L y → ∀ n : ℕ, ∃ a₁ a₂ a₃ : Site 2, (∃ z, z ∉ box 2 n ∧ Connected 2 (removeSites (bc61_boxAround 2 L y) ω) a₁ z) ∧ (∃ z, z ∉ box 2 n ∧ Connected 2 (removeSites (bc61_boxAround 2 L y) ω) a₂ z) ∧ (∃ z, z ∉ box 2 n ∧ Connected 2 (removeSites (bc61_boxAround 2 L y) ω) a₃ z)) ∧ (∀ (R : ℕ) (S : Set (Site 2)) (_ : Fintype (↑S : Type)) (G : SimpleGraph (↑S : Type)) (_ : DecidableRel G.Adj), (∀ v : (↑S : Type), G.degree v = 1 → (v : Site 2) ∈ vertexBoundary 2 R) → (univ.filter (fun v : (↑S : Type) => G.degree v = 1)).card ≤ boxSV_boundaryCard 2 R) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) (c : Fin 2 → Fin (2 * L + 1)), bc75_FiberGnTrifData ω L R c → (bc73_fiber ω L R c).card ≤ boxSV_boundaryCard 2 R) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (y y' : Site 2), numInfiniteClusters 2 ω ≤ 1 → bc61_IsCoarseTrifurcation ω L y → bc61_IsCoarseTrifurcation ω L y' → ∃ a a' : Site 2, (cluster 2 ω a).Infinite ∧ (cluster 2 ω a').Infinite ∧ Connected 2 ω a a') ∧ (numInfiniteClusters 2 bc60_upperLines = ⊤) := by
-- proof
  apply StatMech.Walls.bc87_status


-- created on 2026-10-23
