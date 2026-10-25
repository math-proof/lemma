/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bcvcutvertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc71spanningtree.Part2
import Theorem.StatisticalMechanics.Code.Walls.bgnglobalcontract.Part4
import Instance.StatisticalMechanics.Code.Walls.bcvcutvertex
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


theorem bcv_T0_witness :
    bcv_T0 ≤ bgn_W ∧ bcv_T0.Connected ∧ bcv_T0.degree 0 = 5 ∧ bcv_T0.degree 1 = 3 ∧
      3 ≤ bcv_T0.degree 0 ∧ 3 ≤ bcv_T0.degree 1 := by
  have hle : bcv_T0 ≤ bgn_W := by change ∀ a b, bcv_T0.Adj a b → bgn_W.Adj a b; decide
  have hconn : bcv_T0.Connected := by decide
  exact ⟨hle, hconn, by decide, by decide, (bcv_bgnW_test hle hconn).1, (bcv_bgnW_test hle hconn).2⟩


end StatMech.Walls
