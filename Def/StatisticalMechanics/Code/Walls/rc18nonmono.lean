/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc18nonmono.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc17arbitrary.Part5
import Theorem.StatisticalMechanics.Code.Walls.rc10core.Part4
import Theorem.StatisticalMechanics.Code.Walls.rmr_cylinderwitness
open Finset
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


open Classical in


noncomputable def rc18_cylBoxSupp (A B : Set (ConfigSpace α)) : Finset (Finset α) :=
  univ.filter (fun S => ∃ K L : Finset α, Disjoint K L ∧
    cylinder K (supportCfg S) ⊆ A ∧ cylinder L (supportCfg S) ⊆ B)

end StatMech.Walls
