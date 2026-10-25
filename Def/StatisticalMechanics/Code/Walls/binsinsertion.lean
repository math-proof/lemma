/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/binsinsertion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bcl2close.Part2
import Theorem.StatisticalMechanics.Code.Walls.bcorcorridors.Part5
import Theorem.StatisticalMechanics.Code.Walls.bc117mergeproof.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.HisingBoxClose.Part3
import Theorem.StatisticalMechanics.Code.Walls.binsinsertion
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation
open StatMech.Ising StatMech.IsingFK


namespace StatMech.Walls

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option maxRecDepth 4000


def bins_ExtPred (u₁ u₂ u₃ : Site 2) (ρ : ConfigSpace (Sym2 (Site 2))) : Prop :=
  ((cluster 2 ρ u₁).Infinite ∧ (cluster 2 ρ u₂).Infinite ∧ (cluster 2 ρ u₃).Infinite) ∧
    (cluster 2 ρ u₁ ≠ cluster 2 ρ u₂ ∧ cluster 2 ρ u₁ ≠ cluster 2 ρ u₃ ∧
      cluster 2 ρ u₂ ≠ cluster 2 ρ u₃)


def bins_ExtEvent (I : Finset (Sym2 (Site 2))) (u₁ u₂ u₃ : Site 2) :
    Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | bins_ExtPred u₁ u₂ u₃ (removeSite 0 (bpt2_closeI I ω))}


end StatMech.Walls
