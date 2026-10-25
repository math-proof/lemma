/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskAffineCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamRowDataMaskHall.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskAffineCycle.Part2
open Finset
open Classical


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def leftMaskCyclePair
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) :
    boundarySector ends p.1 ∅ × boundarySector ends p.2 ∅ := by
  have hmid : middleMask m c.1.1 = p.1 := congrArg Prod.fst c.2
  have hout : outerMask m c.1.1 = p.2 := congrArg Prod.snd c.2
  exact
    (⟨colorClass m c.1.1 1,
      ⟨by
        intro e he
        rw [← hmid]
        exact Finset.mem_union_left _ he,
        c.1.2.2.1⟩⟩,
     ⟨colorClass m c.1.1 3,
      ⟨by
        intro e he
        rw [← hout]
        exact Finset.mem_union_right _ he,
        c.1.2.2.2.2.1⟩⟩)


noncomputable def leftMaskCycleEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    leftMaskFiber ends m j k l zero p ↪
      boundarySector ends p.1 ∅ × boundarySector ends p.2 ∅ where
  toFun := leftMaskCyclePair ends m j k l zero p
  inj' := by
    intro c d hcd
    apply Subtype.ext
    apply Subtype.ext
    apply eq_of_middle_outer_colorClass_one_three m c.1.1 d.1.1
    · exact (congrArg Prod.fst c.2).trans (congrArg Prod.fst d.2).symm
    · exact (congrArg Prod.snd c.2).trans (congrArg Prod.snd d.2).symm
    · exact congrArg (fun z => z.1.1) hcd
    · exact congrArg (fun z => z.2.1) hcd


end StatMech.GrahamGHS.FourColor
