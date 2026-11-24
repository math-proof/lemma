module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheWordAlgebra.Part3
open Finset Matrix


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalReduction.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexSectorIntCoordinates {N n : Nat} (x : SixVertexSector N n) :
    Fin n -> Int :=
  fun i => (sixVertexSectorPosition x i).val


end
end StatMech.FrontierD
