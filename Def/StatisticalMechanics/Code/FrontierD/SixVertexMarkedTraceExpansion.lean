/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorPerronLogConcavity.Part3
import Mathlib.Algebra.Polynomial.Eval.Degree
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

open Polynomial


noncomputable def sixVertexShiftedSectorTransferPolynomial
    (N n : Nat) : Matrix (SixVertexSector N n) (SixVertexSector N n) Real[X] := by
  classical
  exact fun x y =>
    if sixVertexSectorRow x = sixVertexSectorRow y then C 2
    else if SixVertexInterlaced
        (sixVertexSectorRow x) (sixVertexSectorRow y) then
      (C 2 + X) ^ sixVertexRowDistance
        (sixVertexSectorRow x) (sixVertexSectorRow y)
    else 0

end
end StatMech.FrontierD
