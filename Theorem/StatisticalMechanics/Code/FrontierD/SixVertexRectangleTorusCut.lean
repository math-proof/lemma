/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleTorusCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleBoundary.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexRectangleTorusCut
open Finset


namespace StatMech.FrontierD

@[simp] theorem finLastOfPos_succ {N : ℕ} (hN : 0 < N) :
    (finLastOfPos hN).succ = Fin.last N := by
  ext
  simp [finLastOfPos, Nat.sub_add_cancel hN]


end StatMech.FrontierD
