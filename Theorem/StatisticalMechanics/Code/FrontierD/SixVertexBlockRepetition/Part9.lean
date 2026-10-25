/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBlockRepetition.Part8
open Finset


namespace StatMech.FrontierD

theorem sixVertexRectangleStraightExtendBoundaryFiber_injective
    {N M r q : ℕ} {ξ : SixVertexToroidalBoundary (N + 1) (M + 1)}
    (z : Fin r → Bool) :
    Function.Injective
      (sixVertexRectangleStraightExtendBoundaryFiber (q := q) (ξ := ξ) z) := by
  intro ω η h
  apply Subtype.ext
  apply sixVertexRectangleStraightExtend_injective z
  exact congrArg Subtype.val h


end StatMech.FrontierD
