/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorCollisionStableSelector
import Mathlib.Data.Prod.Lex
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferOrbit
open Finset


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalMaskTransferAdjacent_symm
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    Symmetric (CanonicalMaskTransferAdjacent ends m j k l zero p) := by
  intro c d h
  rcases h with ⟨q, a, b, hqc, hqd⟩
  exact ⟨q, b, a, hqd, hqc⟩


end StatMech.GrahamGHS.FourColor
