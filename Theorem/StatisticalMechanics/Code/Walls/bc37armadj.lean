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
import Def.StatisticalMechanics.Code.Walls.bc37armadj
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


set_option linter.style.longLine false


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc37_selfDownArm_of_downArmSelector (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bc37_DownArmSelector ω n) : bc36_SelfDownArm ω n := by
  obtain ⟨b, rank, hdata, hrank, hdiv⟩ := h
  refine ⟨b, rank, b, hdata, hrank, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn hlt
  exact ⟨connected_rfl, hdiv x hxbox htri y hybox htriy hxy hconn hlt⟩


theorem bc37_rootedArmDivergence_of_downArmSelector (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bc37_DownArmSelector ω n) : rfp_RootedArmDivergence ω n :=
  bc36_rootedArmDivergence_of_selfDownArm ω n (bc37_selfDownArm_of_downArmSelector ω n h)


end StatMech.Walls
