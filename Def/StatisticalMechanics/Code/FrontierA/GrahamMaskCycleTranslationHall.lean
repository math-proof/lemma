/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskCycleTranslationHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]

open StatMech.Sharpness.RandomCurrent


def rightMaskCycleDifference
    (m : Finset I) (a c : ↑m -> Fin 4) : Finset I :=
  balancedMiddleDifference m a c ∪ balancedOuterDifference m a c


def CrossesRootComponentCut
    (ends : I -> Sym2 W) (K : Finset I) (k : W) (e : I) : Prop :=
  ∃ u v, u ∈ ends e ∧ v ∈ ends e ∧
    u ∉ StatMech.FrontierA.grahamComponentComplement ends K k ∧
    v ∈ StatMech.FrontierA.grahamComponentComplement ends K k


end StatMech.GrahamGHS.FourColor
