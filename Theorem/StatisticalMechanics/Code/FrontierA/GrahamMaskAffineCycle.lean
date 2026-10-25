/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskAffineCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamRowDataMaskHall.Part2
open Finset
open Classical


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem embedding_surjective_of_card_le_two_of_ne
    {A B : Type*} [Fintype A] [Fintype B]
    (f : A ↪ B) (a b : A) (hab : a ≠ b)
    (hB : Fintype.card B ≤ 2) : Function.Surjective f := by
  letI : Nontrivial A := ⟨⟨a, b, hab⟩⟩
  have hone : 1 < Fintype.card A := Fintype.one_lt_card
  have hle : Fintype.card A ≤ Fintype.card B :=
    Fintype.card_le_of_embedding f
  have heq : Fintype.card A = Fintype.card B := by omega
  exact ((Fintype.bijective_iff_injective_and_card f).2
    ⟨f.injective, heq⟩).2


end StatMech.GrahamGHS.FourColor
