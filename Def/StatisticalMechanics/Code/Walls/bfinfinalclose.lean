/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfinfinalclose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bsgspantreegn
import Theorem.StatisticalMechanics.Code.Walls.bcaconcreteclose
import Theorem.StatisticalMechanics.Code.Walls.bfinfinalclose
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


def bfin_SuperCutBridge (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ) : Prop :=
  ∀ y : Site 2, bc67_IsGnTrifurcation ω L y →
    ∃ w₁ w₂ w₃ : Site 2,
      w₁ ≠ bgn_idx L y ∧ w₂ ≠ bgn_idx L y ∧ w₃ ≠ bgn_idx L y ∧
      (bgn_Gn ω L).Adj (bgn_idx L y) w₁ ∧ (bgn_Gn ω L).Adj (bgn_idx L y) w₂ ∧
      (bgn_Gn ω L).Adj (bgn_idx L y) w₃ ∧
      ¬ (bkg_deleteVertex (bgn_Gn ω L) (bgn_idx L y)).Reachable w₁ w₂ ∧
      ¬ (bkg_deleteVertex (bgn_Gn ω L) (bgn_idx L y)).Reachable w₁ w₃ ∧
      ¬ (bkg_deleteVertex (bgn_Gn ω L) (bgn_idx L y)).Reachable w₂ w₃ ∧
      (ray34_AvoidCluster (bgn_Gn ω L) {bgn_idx L y} w₁).Infinite ∧
      (ray34_AvoidCluster (bgn_Gn ω L) {bgn_idx L y} w₂).Infinite ∧
      (ray34_AvoidCluster (bgn_Gn ω L) {bgn_idx L y} w₃).Infinite


def bfin_GlobalArmForest (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ) : Prop :=
  bau_ArmSubforestData ω L R


end StatMech.Walls
