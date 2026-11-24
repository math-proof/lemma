module
public import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorSeededMassObstruction.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
public import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceCarrier.Part3
open Finset SimpleGraph Set


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceCarrier.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

abbrev RlcConnectorFaceVertex (n : Int) :=
  {f : Site 2 // f ∈ rlc_connectorFaceBox n}


end
end StatMech.Universality
