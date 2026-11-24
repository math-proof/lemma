module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part13
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

noncomputable instance sixVertexNoAdjacentSectorFintype (N n : Nat) :
    Fintype (SixVertexNoAdjacentSector N n) :=
  Fintype.ofFinite _


end
end StatMech.FrontierD
