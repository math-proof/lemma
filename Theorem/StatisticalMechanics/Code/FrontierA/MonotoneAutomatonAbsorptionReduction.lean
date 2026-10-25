/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonAbsorptionReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonStep3Bridge.Part4
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonAbsorptionReduction
open MeasureTheory Set
open scoped ENNReal


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


theorem measurableSet_pairDisjointInfiniteHighAt (x : Site d) :
    MeasurableSet (pairDisjointInfiniteHighAt x) := by
  exact (measurableSet_pairHighInfinite x).inter
    (measurableSet_pairHighCluster_meets_lowInfinite x).compl


end StatMech.FrontierA
