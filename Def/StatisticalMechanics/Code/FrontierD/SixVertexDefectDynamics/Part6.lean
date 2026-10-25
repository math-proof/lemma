/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part13
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDefectDynamics.Part5
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexDefectLowerMoveSector
    {N n : Nat} (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) (hn : 0 < n)
    (i : Fin n) (hd : 0 < sixVertexSectorGapDefects x i)
    (hlast : (sixVertexSectorPosition x ⟨n - 1, by omega⟩).val +
      sixVertexDefectLowerAdvance i ⟨n - 1, by omega⟩ < N) :
    SixVertexSector N n :=
  sixVertexForwardMoveSector x (sixVertexDefectLowerAdvance i)
    (sixVertexDefectLowerMove_bound x hx hn i hd hlast)
    (sixVertexDefectLowerMove_mono x hx i hd)

end
end StatMech.FrontierD
