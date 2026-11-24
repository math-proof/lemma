module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerron.Part9
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexParticleHole
open Finset Matrix


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexParticleHole.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

def sixVertexSectorPrefixCount {N n : ℕ}
    (x : SixVertexSector N n) (k : Fin N) : ℕ :=
  #{j ∈ (x : Finset (Fin N)) | j ≤ k}

end StatMech.FrontierD
