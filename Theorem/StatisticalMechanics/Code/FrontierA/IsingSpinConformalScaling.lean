/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSpinConformalScaling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSpinConformalReduction
import Def.StatisticalMechanics.Code.FrontierA.IsingSpinConformalScaling
open Filter Topology
open scoped BigOperators


namespace StatMech.FrontierA

theorem spinMeshRenormalization_eq_card_div_eight
    (iota : Type*) [Fintype iota] (delta : Real) :
    spinMeshRenormalization iota delta =
      delta ^ (-(Fintype.card iota : Real) / 8) := by
  unfold spinMeshRenormalization isingSpinScalingDimension
  congr 1
  ring


end StatMech.FrontierA
