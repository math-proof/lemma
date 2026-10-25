/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDisagreementComponentCType.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopTopology.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusMedial.Part5
import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem finsetOther_mem
    {α : Type*} [DecidableEq α] (s : Finset α) (d : α)
    (hcard : s.card = 2) (hd : d ∈ s) :
    finsetOther s d hcard hd ∈ s :=
  (Classical.choose_spec
    (existsUnique_mem_ne_of_card_eq_two s d hcard hd)).1.1

theorem finsetOther_ne
    {α : Type*} [DecidableEq α] (s : Finset α) (d : α)
    (hcard : s.card = 2) (hd : d ∈ s) :
    finsetOther s d hcard hd ≠ d :=
  (Classical.choose_spec
    (existsUnique_mem_ne_of_card_eq_two s d hcard hd)).1.2

theorem finsetOther_involutive
    {α : Type*} [DecidableEq α] (s : Finset α) (d : α)
    (hcard : s.card = 2) (hd : d ∈ s) :
    finsetOther s (finsetOther s d hcard hd) hcard
        (finsetOther_mem s d hcard hd) = d := by
  symm
  apply (Classical.choose_spec
    (existsUnique_mem_ne_of_card_eq_two s
      (finsetOther s d hcard hd) hcard
      (finsetOther_mem s d hcard hd))).2
  exact ⟨hd, (finsetOther_ne s d hcard hd).symm⟩


end
end StatMech.FrontierD
