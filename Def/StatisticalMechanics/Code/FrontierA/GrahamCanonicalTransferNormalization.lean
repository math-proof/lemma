/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferNormalization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferFailedGate
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferNormalization
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def canonicalNormalRow
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (c : ↑m -> Fin 4) : Finset I :=
  rowClass m c 0 ∆ canonicalTransferUnion ends m k zero c


end StatMech.GrahamGHS.FourColor
