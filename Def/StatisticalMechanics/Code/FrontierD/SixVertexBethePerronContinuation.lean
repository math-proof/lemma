/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseSingle.Part3
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

def sixVertexSectorTransferInfinity (N n : Nat) :
    Matrix (SixVertexSector N n) (SixVertexSector N n) Real := by
  classical
  exact fun x y =>
    if x ≠ y ∧ SixVertexInterlaced (sixVertexSectorRow x)
        (sixVertexSectorRow y) ∧
        sixVertexRowDistance (sixVertexSectorRow x)
          (sixVertexSectorRow y) = 2 * n then 1 else 0

end
end StatMech.FrontierD
