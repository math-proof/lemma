/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferGF2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferCoverageJoin.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferGF2
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def canonicalTranslatedRow
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (r c : ↑m -> Fin 4) : Finset I :=
  rowClass m c 0 ∆ canonicalTransferUnion ends m k zero r


def RowSupportDisconnects
    (ends : I -> Sym2 W) (m K : Finset I) (k zero : W) : Prop :=
  ¬ StatMech.Sharpness.RandomCurrent.connK ends K k zero ∧
    ¬ StatMech.Sharpness.RandomCurrent.connK ends (m \ K) k zero


end StatMech.GrahamGHS.FourColor
