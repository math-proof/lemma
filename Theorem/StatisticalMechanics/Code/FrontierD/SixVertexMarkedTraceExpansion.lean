/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedTraceExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexSectorPerronLogConcavity.Part3
import Mathlib.Algebra.Polynomial.Eval.Degree
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedTraceExpansion
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

open Polynomial


theorem eval_sixVertexShiftedSectorTransferPolynomial_apply
    (N n : Nat) (t : Real) (x y : SixVertexSector N n) :
    eval t (sixVertexShiftedSectorTransferPolynomial N n x y) =
      sixVertexSectorTransfer N n (2 + t) x y := by
  classical
  unfold sixVertexShiftedSectorTransferPolynomial sixVertexSectorTransfer
  unfold sixVertexTransfer
  by_cases hxy : sixVertexSectorRow x = sixVertexSectorRow y
  · simp [hxy]
  · by_cases hinter : SixVertexInterlaced
        (sixVertexSectorRow x) (sixVertexSectorRow y)
    · simp [hxy, hinter]
    · simp [hxy, hinter]

theorem map_sixVertexShiftedSectorTransferPolynomial
    (N n : Nat) (t : Real) :
    (sixVertexShiftedSectorTransferPolynomial N n).map (evalRingHom t) =
      sixVertexSectorTransfer N n (2 + t) := by
  ext x y
  exact eval_sixVertexShiftedSectorTransferPolynomial_apply N n t x y


end
end StatMech.FrontierD
