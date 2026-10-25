/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bptpartitioncount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bsdsepdegree
import Theorem.StatisticalMechanics.Code.Walls.bc69count.Part2
import Theorem.StatisticalMechanics.Code.Walls.bkgclassicalforest.Part2
import Def.StatisticalMechanics.Code.Walls.bptpartitioncount
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bpt_mem_boundaryClass {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ} {x a c : Site d} :
    c ∈ bpt_boundaryClass ω L R x a ↔
      c ∈ vertexBoundary d R ∧ (bc67_contractedLattice ω L x).Reachable a c :=
  Iff.rfl


theorem bpt_trif_three_boundary_classes (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hR : 1 ≤ R)
    {x : Site d} (arm : Fin 3 → Site d)
    (harmbox : ∀ i, arm i ∈ box d R)
    (harmne : ∀ i, arm i ≠ x)
    (harminf : ∀ i, (cluster d (removeSites (bc61_boxAround d L x) ω) (arm i)).Infinite)
    (harmsep : ∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (arm i) (arm j)) :
    ∃ t : Fin 3 → Site d,
      (∀ i, t i ∈ vertexBoundary d R) ∧
      (∀ i, t i ≠ x) ∧
      Function.Injective (fun i => (bc67_contractedLattice ω L x).connectedComponentMk (t i)) := by
  classical
  obtain ⟨t, hbdry, hreach, hne, hsep⟩ :=
    bsd_arm_tips_of_separated ω L R hR arm harmbox harmne harminf harmsep
  refine ⟨t, hbdry, hne, ?_⟩
  intro i j hij
  by_contra hij'
  exact hsep i j hij' (SimpleGraph.ConnectedComponent.eq.mp hij)


theorem bpt_trif_three_classes_disjoint (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hR : 1 ≤ R)
    {x : Site d} (arm : Fin 3 → Site d)
    (harmbox : ∀ i, arm i ∈ box d R)
    (harmne : ∀ i, arm i ≠ x)
    (harminf : ∀ i, (cluster d (removeSites (bc61_boxAround d L x) ω) (arm i)).Infinite)
    (harmsep : ∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (arm i) (arm j)) :
    ∃ t : Fin 3 → Site d,
      (∀ i, t i ∈ bpt_boundaryClass ω L R x (t i)) ∧
      (∀ i j, i ≠ j → Disjoint (bpt_boundaryClass ω L R x (t i)) (bpt_boundaryClass ω L R x (t j))) := by
  classical
  obtain ⟨t, hbdry, hreach, hne, hsep⟩ :=
    bsd_arm_tips_of_separated ω L R hR arm harmbox harmne harminf harmsep
  refine ⟨t, ?_, ?_⟩
  · intro i; exact ⟨hbdry i, SimpleGraph.Reachable.refl _⟩
  · intro i j hij
    rw [Set.disjoint_left]
    rintro c ⟨_, hci⟩ ⟨_, hcj⟩
    exact hsep i j hij (hci.trans hcj.symm)


theorem bpt_sameTrif_classes_laminar (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (x a b : Site d) :
    bpt_boundaryClass ω L R x a = bpt_boundaryClass ω L R x b ∨
      Disjoint (bpt_boundaryClass ω L R x a) (bpt_boundaryClass ω L R x b) := by
  by_cases h : (bc67_contractedLattice ω L x).Reachable a b
  · left
    ext c
    simp only [bpt_mem_boundaryClass]
    constructor
    · rintro ⟨hc, hac⟩; exact ⟨hc, h.symm.trans hac⟩
    · rintro ⟨hc, hbc⟩; exact ⟨hc, h.trans hbc⟩
  · right
    rw [Set.disjoint_left]
    rintro c ⟨_, hac⟩ ⟨_, hbc⟩
    exact h (hac.trans hbc.symm)


end StatMech.Walls
