module
public import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceScaleOneAudit.Part2
public import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFacePositionedObstruction
open Finset SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFacePositionedObstruction.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def rlc_axisReturnCounterexampleClosedConfig :
    ConfigSpace (Sym2 (RlcConnectorVertex 1)) :=
  fun _ => false

end
end StatMech.Universality
