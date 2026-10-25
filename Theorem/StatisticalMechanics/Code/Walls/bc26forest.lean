/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc26forest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.ArmEndDisjointClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsFinal.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Walls.bc24coarsetrif.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc25renormcount
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc26_arms_globalCut_pairwise_disconnected (T : Finset (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) {x : Site d} (hxT : x ∈ T)
    (htri : IsTrifurcation d ω x) :
    ∃ a₁ a₂ a₃ : Site d,
      (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
      (Connected d ω x a₁ ∧ Connected d ω x a₂ ∧ Connected d ω x a₃) ∧
      ((cluster d ω a₁).Infinite ∧ (cluster d ω a₂).Infinite ∧ (cluster d ω a₃).Infinite) ∧
      (¬ Connected d (removeSites T ω) a₁ a₂ ∧
        ¬ Connected d (removeSites T ω) a₁ a₃ ∧
        ¬ Connected d (removeSites T ω) a₂ a₃) := by
  obtain ⟨a₁, a₂, a₃, hne, hconn, hinf, hsep⟩ := htri
  refine ⟨a₁, a₂, a₃, hne, hconn, hinf, ?_, ?_, ?_⟩
  · exact daep2_globalCut_disconnected_of_singleCut T ω hxT hsep.1
  · exact daep2_globalCut_disconnected_of_singleCut T ω hxT hsep.2.1
  · exact daep2_globalCut_disconnected_of_singleCut T ω hxT hsep.2.2


theorem bc26_two_arms_avoid_vertex (ω : ConfigSpace (Sym2 (Site d)))
    {x a₁ a₂ a₃ : Site d}
    (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
    (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
    (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) (y : Site d) :
    (¬ Connected d (removeSite x ω) a₁ y ∧ ¬ Connected d (removeSite x ω) a₂ y) ∨
    (¬ Connected d (removeSite x ω) a₁ y ∧ ¬ Connected d (removeSite x ω) a₃ y) ∨
    (¬ Connected d (removeSite x ω) a₂ y ∧ ¬ Connected d (removeSite x ω) a₃ y) :=
  daep2_two_branches_avoid ω hd12 hd13 hd23 y


theorem bc26_avoiding_arm_of_trif (ω : ConfigSpace (Sym2 (Site d)))
    {x : Site d} (htri : IsTrifurcation d ω x) (y : Site d) :
    ∃ a : Site d, Connected d ω x a ∧ (cluster d ω a).Infinite ∧
      ¬ bkfl_inArm ω x a y := by
  obtain ⟨a₁, a₂, a₃, _hne, hconn, hinf, hsep⟩ := htri
  rcases bc26_two_arms_avoid_vertex ω hsep.1 hsep.2.1 hsep.2.2 y with
    ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h2, _⟩
  · exact ⟨a₁, hconn.1, hinf.1, h1⟩
  · exact ⟨a₁, hconn.1, hinf.1, h1⟩
  · exact ⟨a₂, hconn.2.1, hinf.2.1, h2⟩


end StatMech.Walls
