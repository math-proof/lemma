/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc53butterfly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc52pairimage
import Theorem.StatisticalMechanics.Code.Walls.rc46butterfly.Part3
import Theorem.StatisticalMechanics.Code.Walls.rc38butterflymono
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerDoubled.Part6
import Instance.StatisticalMechanics.Code.Walls.rc53butterfly
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


def rc53_cubeFillCount {n : ℕ} (F : Finset (Finset (Fin n ⊕ Fin n))) : ℕ :=
  (F.filter rc53_isCubeFilling).card


end StatMech.Walls
