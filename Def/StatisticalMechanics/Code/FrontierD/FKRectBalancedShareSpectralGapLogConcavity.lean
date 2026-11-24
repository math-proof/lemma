module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceSpectralSchedule.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveEvenTraceLogConcavity.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBalancedShareSpectralGapLogConcavity
open Filter MeasureTheory Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBalancedShareSpectralGapLogConcavity.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

open StatMech.FK StatMech.Lattice StatMech.Percolation StatMech.BeffaraDC

noncomputable section

def SixVertexCanonicalPositiveEvenTraceKeyCapacityHall : Prop :=
  forall r k : Nat,
    SixVertexPositiveEvenTraceKeyCapacityHall
      (sixVertexFourWidth r (k + 1))
      (sixVertexFourWidth_pos r (k + 1))
      (sixVertexFourWidth_even r (k + 1))


end
end StatMech.FrontierD
