/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc32forestsep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.ArmReachComponentClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc26forest.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc30armforest.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc31globalarm.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc32_not_tfree_of_branchTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ a aⱼ y : Site d} (hmeet : Connected d (removeSite x₀ ω) a aⱼ)
    (hyj : Connected d (removeSite x₀ ω) aⱼ y) (hyT : y ∈ tfc_trifFinset ω n) :
    ¬ (∀ z, Connected d (removeSite x₀ ω) a z → z ∉ tfc_trifFinset ω n) := by
  intro hTfree
  exact hTfree y (hmeet.trans hyj) hyT


theorem bc32_no_tfreeArm_of_armTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ a₁ a₂ a₃ : Site d} (y : Fin 3 → Site d)
    (htrifArm : ∀ i, y i ∈ tfc_trifFinset ω n ∧
      Connected d (removeSite x₀ ω) (![a₁, a₂, a₃] i) (y i))
    {a : Site d}
    (hcover : Connected d (removeSite x₀ ω) a a₁ ∨
      Connected d (removeSite x₀ ω) a a₂ ∨ Connected d (removeSite x₀ ω) a a₃) :
    ¬ (∀ z, Connected d (removeSite x₀ ω) a z → z ∉ tfc_trifFinset ω n) := by
  rcases hcover with h | h | h
  · exact bc32_not_tfree_of_branchTrif ω n h (htrifArm 0).2 (htrifArm 0).1
  · exact bc32_not_tfree_of_branchTrif ω n h (htrifArm 1).2 (htrifArm 1).1
  · exact bc32_not_tfree_of_branchTrif ω n h (htrifArm 2).2 (htrifArm 2).1


theorem bc32_not_tfreeDownArmData_of_clawTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) {x₀ a₁ a₂ a₃ : Site d} (y : Fin 3 → Site d)
    (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (htrifArm : ∀ i, y i ∈ tfc_trifFinset ω n ∧
      Connected d (removeSite x₀ ω) (![a₁, a₂, a₃] i) (y i))
    (hcover : ∀ a : Site d, (cluster d (removeSite x₀ ω) a).Infinite →
      Connected d ω x₀ a →
      Connected d (removeSite x₀ ω) a a₁ ∨
        Connected d (removeSite x₀ ω) a a₂ ∨ Connected d (removeSite x₀ ω) a a₃) :
    ¬ bc31_TfreeDownArmData ω n rank := by
  rintro ⟨b, hbdata, _⟩
  obtain ⟨_, hbconn, hbinf, hbTfree⟩ := hbdata x₀ hx0box htri0
  exact bc32_no_tfreeArm_of_armTrif ω n y htrifArm (hcover (b x₀) hbinf hbconn) hbTfree


end StatMech.Walls
