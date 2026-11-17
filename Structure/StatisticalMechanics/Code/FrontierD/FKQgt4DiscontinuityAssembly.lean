/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4DiscontinuityAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4CorrelationReduction
public import Theorem.StatisticalMechanics.Code.FK.OrderTransition.Part2
public import Theorem.StatisticalMechanics.Code.FK.TwoPointPositiveFull
public import Theorem.StatisticalMechanics.Code.FK.FreeTailTriviality
public import Theorem.StatisticalMechanics.Code.FK.FKGeneralQClusterFKG
public import Theorem.StatisticalMechanics.Code.BeffaraDC.SelfDualValue
public import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4DiscontinuityAssembly.Part2
open MeasureTheory Filter Topology


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation

public noncomputable section

structure FKQgt4TorusSixVertexWindingBridge (xiInv R : Real) : Prop where
  oneWinding : R <= xiInv
  fixedCharge : forall r : Nat, 2 <= r ->
    ((r - 1 : Nat) : Real) * xiInv <= (r : Real) * R

end
end StatMech.FrontierD
