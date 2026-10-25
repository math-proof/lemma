/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bxpxpos.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bmfmergefree.Part2
import Theorem.StatisticalMechanics.Code.Percolation.AvoidingAttachment.Part3
import Theorem.StatisticalMechanics.Code.Percolation.PrivateArmProve.Part2
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationConstruction.Part3
import Theorem.StatisticalMechanics.Code.Walls.bxpxpos
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace


namespace StatMech.Walls

open StatMech.Percolation

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option maxRecDepth 4000


variable {d : ℕ}


def bxp_Y : Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω |
    ((0 : Site 2) ∉ cluster 2 ω bmf_b₁ ∧ (0 : Site 2) ∉ cluster 2 ω bmf_b₂ ∧
      (0 : Site 2) ∉ cluster 2 ω bmf_b₃) ∧
    ((cluster 2 ω bmf_b₁).Infinite ∧ (cluster 2 ω bmf_b₂).Infinite ∧
      (cluster 2 ω bmf_b₃).Infinite) ∧
    (¬ Connected 2 ω bmf_b₁ bmf_b₂ ∧ ¬ Connected 2 ω bmf_b₁ bmf_b₃ ∧
      ¬ Connected 2 ω bmf_b₂ bmf_b₃)}


end StatMech.Walls
