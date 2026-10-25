/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc37armadj.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Percolation.ForestSelectorProve.Part7
import Theorem.StatisticalMechanics.Code.Percolation.RootedForestPeelClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeArmClose.Part3
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeTrifClose.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc26forest.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc35globalarm
import Theorem.StatisticalMechanics.Code.Walls.bc36rooteddiv.Part2
import Def.StatisticalMechanics.Code.Walls.bc37armadj.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


set_option linter.style.longLine false


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc37_armAdjacent_symm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) {x y : Site d}
    (h : bc37_ArmAdjacent ω n x y) : bc37_ArmAdjacent ω n y x := by
  obtain ⟨hne, hconn, hcut⟩ := h
  refine ⟨hne.symm, hconn.symm, ?_⟩
  have hset : ((tfc_trifFinset ω n).erase y).erase x
      = ((tfc_trifFinset ω n).erase x).erase y := Finset.erase_right_comm
  unfold bc37_cutExcept
  rw [hset]
  exact hcut.symm


theorem bc37_armAdjacent_irrefl (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (x : Site d) :
    ¬ bc37_ArmAdjacent ω n x x := fun ⟨hne, _, _⟩ => hne rfl


end StatMech.Walls
