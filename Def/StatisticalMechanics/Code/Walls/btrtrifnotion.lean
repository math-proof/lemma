/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/btrtrifnotion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bfkforestbuild
import Theorem.StatisticalMechanics.Code.Walls.btrtrifnotion
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


def btr_IsGenuineCoarseTrif (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) : Prop :=
  ∃ a₁ a₂ a₃ : Site d,
    (∃ b₁ ∈ bc61_boxAround d L y, (openSubgraph d ω).Adj b₁ a₁) ∧
    (∃ b₂ ∈ bc61_boxAround d L y, (openSubgraph d ω).Adj b₂ a₂) ∧
    (∃ b₃ ∈ bc61_boxAround d L y, (openSubgraph d ω).Adj b₃ a₃) ∧
    
    (Connected d ω y a₁ ∧ Connected d ω y a₂ ∧ Connected d ω y a₃) ∧
    ((cluster d (removeSites (bc61_boxAround d L y) ω) a₁).Infinite ∧
     (cluster d (removeSites (bc61_boxAround d L y) ω) a₂).Infinite ∧
     (cluster d (removeSites (bc61_boxAround d L y) ω) a₃).Infinite) ∧
    (¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₂ ∧
     ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₁ a₃ ∧
     ¬ Connected d (removeSites (bc61_boxAround d L y) ω) a₂ a₃)


end StatMech.Walls
