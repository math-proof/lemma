import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc116armproof
open Set SimpleGraph Finset StatMech StatMech.Walls


/--
[bc116_isInternal_of_mem_support_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc116armproof.lean)
-/
@[path]
private lemma bc116_isInternal_of_mem_support_free_eq
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
  apply StatMech.Walls.bc116_isInternal_of_mem_support_free F p hp hv hvs hvt

/--
[bc116_isInternal_of_throughPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc116armproof.lean)
-/
@[path]
private lemma bc116_isInternal_of_throughPath_eq
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
  apply StatMech.Walls.bc116_isInternal_of_throughPath F p hp hv hvs hvt

/--
[bc116_armCovered_of_throughPathCovered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc116armproof.lean)
-/
@[path]
private lemma bc116_armCovered_of_throughPathCovered_eq
  {G : SimpleGraph V}
  {F : SimpleGraph V}
  {B H : V → Prop}
-- given
  (hcov : bc116_ThroughPathCovered F B H) :
-- imply
  bc114_ArmCovered F B H := by
-- proof
  apply StatMech.Walls.bc116_armCovered_of_throughPathCovered F hcov

/--
[bc116_path_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc116armproof.lean)
-/
@[path]
private lemma bc116_path_of_reachable_eq
  {F : SimpleGraph V}
  {a z : V}
-- given
  (hr : F.Reachable a z) :
-- imply
  ∃ p : F.Walk a z, p.IsPath := by
-- proof
  apply StatMech.Walls.bc116_path_of_reachable F hr

/--
[bc116_interior_of_arm_path_covered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc116armproof.lean)
-/
@[path]
private lemma bc116_interior_of_arm_path_covered_eq
  {F : SimpleGraph V}
  {a z v : V}
-- given
  (hva : v ≠ a)
  (hvz : v ≠ z)
  (hmem : ∃ p : F.Walk a z, p.IsPath ∧ v ∈ p.support) :
-- imply
  bc114_IsInternal F v := by
-- proof
  apply StatMech.Walls.bc116_interior_of_arm_path_covered F hva hvz hmem

/--
[bc116_covered_of_on_hub_boundary_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc116armproof.lean)
-/
@[path]
private lemma bc116_covered_of_on_hub_boundary_path_eq
  {F : SimpleGraph V}
  {s t v : V}
  {p : F.Walk s t}
-- given
  (hp : p.IsPath)
  (hmem : v ∈ p.support)
  (hvs : v ≠ s)
  (hvt : v ≠ t) :
-- imply
  bc114_IsInternal F v := by
-- proof
  apply StatMech.Walls.bc116_covered_of_on_hub_boundary_path F p hp hmem hvs hvt

/--
[bc116_leaf_on_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc116armproof.lean)
-/
@[path]
private lemma bc116_leaf_on_boundary_eq
  [Fintype V]
  [DecidableEq V]
  {F : SimpleGraph V}
  [DecidableRel F.Adj]
  {B H : V → Prop}
  {v : V}
-- given
  (hcov : bc116_ThroughPathCovered F B H)
  (hhub : ∀ v, H v → 3 ≤ F.degree v)
  (hdeg : F.degree v = 1) :
-- imply
  B v := by
-- proof
  apply StatMech.Walls.bc116_leaf_on_boundary F hcov hhub hdeg

/--
[bc116_armForest_boundaryAnchored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc116armproof.lean)
-/
@[path]
private lemma bc116_armForest_boundaryAnchored_eq
  [Fintype V]
  [DecidableEq V]
  {F : SimpleGraph V}
  [DecidableRel F.Adj]
  {B H : V → Prop}
-- given
  (hcov : bc116_ThroughPathCovered F B H)
  (hhub : ∀ v, H v → 3 ≤ F.degree v)
  (hac : F.IsAcyclic)
  (hmin : ∀ v, 1 ≤ F.degree v) :
-- imply
  F.IsAcyclic ∧ (∀ v, 1 ≤ F.degree v) ∧ (∀ v, F.degree v = 1 → B v) := by
-- proof
  apply StatMech.Walls.bc116_armForest_boundaryAnchored F hcov hhub hac hmin

/--
[bc116_pendant_not_covered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc116armproof.lean)
-/
@[path]
private lemma bc116_pendant_not_covered_eq
  [Fintype V]
  [DecidableEq V]
  {F : SimpleGraph V}
  [DecidableRel F.Adj]
  {v : V}
-- given
  (hdeg : F.degree v = 1) :
-- imply
  ¬ bc114_IsInternal F v := by
-- proof
  apply StatMech.Walls.bc116_pendant_not_covered F hdeg

/--
[bc116_covered_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc116armproof.lean)
-/
@[path]
private lemma bc116_covered_nonvacuous_eq
  [Fintype V]
  [DecidableEq V] :
-- imply
  bc114_IsInternal (SimpleGraph.fromEdgeSet {s((0 : Fin 3), 1), s((1 : Fin 3), 2)}) 1 := by
-- proof
  apply StatMech.Walls.bc116_covered_nonvacuous

/--
[bc116_arm_boundary_path_concrete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc116armproof.lean)
-/
@[path]
private lemma bc116_arm_boundary_path_concrete_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {y a : Site d}
-- given
  (hR : 1 ≤ R)
  (habox : a ∈ box d R)
  (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
-- imply
  ∃ z ∈ vertexBoundary d R, ∃ _p : (bc67_contractedLattice ω L y).Walk a z, True := by
-- proof
  apply StatMech.Walls.bc116_arm_boundary_path_concrete ω L R hR y a habox hinf

/--
[bc116_arm_interior_covered_concrete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc116armproof.lean)
-/
@[path]
private lemma bc116_arm_interior_covered_concrete_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y a z v : Site d}
-- given
  (hva : v ≠ a)
  (hvz : v ≠ z)
  (hmem : ∃ p : (bc67_contractedLattice ω L y).Walk a z, p.IsPath ∧ v ∈ p.support) :
-- imply
  bc114_IsInternal (bc67_contractedLattice ω L y) v := by
-- proof
  apply StatMech.Walls.bc116_arm_interior_covered_concrete ω L y a z v hva hvz hmem

/--
[bc116_armCovered_concrete_of_membership](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc116armproof.lean)
-/
@[path]
private lemma bc116_armCovered_concrete_of_membership_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d}
  {B H : Site d → Prop}
-- given
  (hmem : bc116_ArmPathMembership ω L y B H) :
-- imply
  bc114_ArmCovered (bc67_contractedLattice ω L y) B H := by
-- proof
  apply StatMech.Walls.bc116_armCovered_concrete_of_membership ω L y hmem

/--
[bc116_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc116armproof.lean)
-/
@[path]
private lemma bc116_status_eq
  {d : ℕ} :
-- imply
  (∀ (F : SimpleGraph V) (B H : V → Prop), bc116_ThroughPathCovered F B H → bc114_ArmCovered F B H) ∧ (∀ (F : SimpleGraph V) (v : V), bc114_IsInternal F v → ∃ (s t : V) (p : F.Walk s t), p.IsPath ∧ v ∈ p.support ∧ v ≠ s ∧ v ≠ t) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 1 ≤ R → ∀ (y a : Site d), a ∈ box d R → (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite → ∃ z ∈ vertexBoundary d R, ∃ _p : (bc67_contractedLattice ω L y).Walk a z, True) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) (B H : Site d → Prop), bc116_ArmPathMembership ω L y B H → bc114_ArmCovered (bc67_contractedLattice ω L y) B H) ∧ (∀ (F : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel F.Adj] (v : V), F.degree v = 1 → ¬ bc114_IsInternal F v) := by
-- proof
  apply StatMech.Walls.bc116_status


-- created on 2026-10-23
