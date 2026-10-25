/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerronNoAdjacent.Part2
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexSectorTransferNormalized
    (N n : Nat) (c : Real) : Matrix (SixVertexSector N n)
      (SixVertexSector N n) Real :=
  fun x y => sixVertexSectorTransfer N n c x y / (c ^ 2 - 2) ^ n


def sixVertexSectorTransferNormalizedMaxRowSum
    (N n : Nat) (hn : n ≤ N) (c : Real) : Real :=
  letI : Nonempty (SixVertexSector N n) := sixVertexSector_nonempty hn
  (Finset.univ : Finset (SixVertexSector N n)).sup'
    Finset.univ_nonempty
    (fun x => ∑ y, sixVertexSectorTransferNormalized N n c x y)


end
end StatMech.FrontierD
