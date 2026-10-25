/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc116armproof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc114haschild.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc101mengergap
import Def.StatisticalMechanics.Code.Walls.bc116armproof
open Set SimpleGraph Finset

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

variable {V : Type*}

variable {G : SimpleGraph V}


theorem bc116_armCovered_of_throughPathCovered (F : SimpleGraph V) {B H : V → Prop}
    (hcov : bc116_ThroughPathCovered F B H) : bc114_ArmCovered F B H := by
  intro v hvB hvH
  obtain ⟨s, t, p, hp, hmem, hvs, hvt⟩ := hcov v hvB hvH
  exact bc116_isInternal_of_throughPath F p hp hmem hvs hvt

end StatMech.Walls


namespace StatMech.Walls

variable {V : Type*}


theorem bc116_path_of_reachable (F : SimpleGraph V) {a z : V} (hr : F.Reachable a z) :
    ∃ p : F.Walk a z, p.IsPath :=
  ⟨hr.exists_path_of_dist.choose, hr.exists_path_of_dist.choose_spec.1⟩


theorem bc116_interior_of_arm_path_covered (F : SimpleGraph V) {a z v : V}
    (hva : v ≠ a) (hvz : v ≠ z)
    (hmem : ∃ p : F.Walk a z, p.IsPath ∧ v ∈ p.support) :
    bc114_IsInternal F v := by
  obtain ⟨p, hp, hvp⟩ := hmem
  exact bc116_isInternal_of_mem_support_free F p hp hvp hva hvz


theorem bc116_covered_of_on_hub_boundary_path (F : SimpleGraph V) {s t v : V}
    (p : F.Walk s t) (hp : p.IsPath) (hmem : v ∈ p.support) (hvs : v ≠ s) (hvt : v ≠ t) :
    bc114_IsInternal F v :=
  bc116_isInternal_of_mem_support_free F p hp hmem hvs hvt

end StatMech.Walls


namespace StatMech.Walls

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem bc116_leaf_on_boundary (F : SimpleGraph V) [DecidableRel F.Adj] {B H : V → Prop}
    (hcov : bc116_ThroughPathCovered F B H) (hhub : ∀ v, H v → 3 ≤ F.degree v)
    {v : V} (hdeg : F.degree v = 1) : B v :=
  bc114_leaf_on_boundary_of_armCovered F (bc116_armCovered_of_throughPathCovered F hcov) hhub hdeg


theorem bc116_armForest_boundaryAnchored (F : SimpleGraph V) [DecidableRel F.Adj] {B H : V → Prop}
    (hcov : bc116_ThroughPathCovered F B H) (hhub : ∀ v, H v → 3 ≤ F.degree v)
    (hac : F.IsAcyclic) (hmin : ∀ v, 1 ≤ F.degree v) :
    F.IsAcyclic ∧ (∀ v, 1 ≤ F.degree v) ∧ (∀ v, F.degree v = 1 → B v) :=
  bc114_armForest_boundaryAnchored F (bc116_armCovered_of_throughPathCovered F hcov) hhub hac hmin


theorem bc116_pendant_not_covered (F : SimpleGraph V) [DecidableRel F.Adj] {v : V}
    (hdeg : F.degree v = 1) : ¬ bc114_IsInternal F v :=
  bc114_leaf_not_internal F hdeg


theorem bc116_covered_nonvacuous :
    bc114_IsInternal (SimpleGraph.fromEdgeSet {s((0 : Fin 3), 1), s((1 : Fin 3), 2)}) 1 :=
  bc114_armCovered_nonvacuous

end StatMech.Walls


namespace StatMech.Walls

open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}


theorem bc116_arm_boundary_path_concrete (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hR : 1 ≤ R)
    (y a : Site d) (habox : a ∈ box d R)
    (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
    ∃ z ∈ vertexBoundary d R, ∃ _p : (bc67_contractedLattice ω L y).Walk a z, True := by
  obtain ⟨z, hzb, hrz⟩ := bc101_arm_reaches_boundary ω L R hR y a habox hinf
  obtain ⟨p, _hp⟩ := bc116_path_of_reachable (bc67_contractedLattice ω L y) hrz
  exact ⟨z, hzb, p, trivial⟩


theorem bc116_arm_interior_covered_concrete (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ)
    (y a z v : Site d) (hva : v ≠ a) (hvz : v ≠ z)
    (hmem : ∃ p : (bc67_contractedLattice ω L y).Walk a z, p.IsPath ∧ v ∈ p.support) :
    bc114_IsInternal (bc67_contractedLattice ω L y) v :=
  bc116_interior_of_arm_path_covered (bc67_contractedLattice ω L y) hva hvz hmem


end StatMech.Walls
