/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc21persupport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc20reflection.Part5
import Def.StatisticalMechanics.Code.Walls.rc21persupport.Part3
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc21_localReflSearch_fin2_refuted :
    rc21_localReflSearch 2 ({∅, {0}, {1}} : Finset (Finset (Fin 2)))
      ({{0}, {1}, {0, 1}} : Finset (Finset (Fin 2))) = false := by
  decide


end StatMech.Walls
