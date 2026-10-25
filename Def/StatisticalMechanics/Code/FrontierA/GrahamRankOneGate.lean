/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamRankOneGate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskAffineCycle.Part6
open Finset
open Classical
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


def RootSpanning (ends : I → Sym2 W) (S : Finset I) (root : W) : Prop :=
  ∀ i ∈ S, ∀ x ∈ ends i, connK ends S root x


end StatMech.GrahamGHS.FourColor
