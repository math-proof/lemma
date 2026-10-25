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
import Def.StatisticalMechanics.Code.Walls.bc26forest
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc26_globalForestArms_of_globalCutArmData (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bc26_GlobalCutArmData ω n) : aed_GlobalForestArms ω n :=
  h


theorem bc26_Tcount_le_boundary_of_globalCutArmData (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : bc26_GlobalCutArmData ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  aed_Tcount_le_boundary_of_globalForestArms ω n hn
    (bc26_globalForestArms_of_globalCutArmData ω n h)


end StatMech.Walls
