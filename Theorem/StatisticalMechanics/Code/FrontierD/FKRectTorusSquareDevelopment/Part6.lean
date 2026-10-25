/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDevelopedWinding.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part6


namespace StatMech.FrontierD

noncomputable section

theorem fkRectVertexSquareClass_injective (R : FKRectTorus) :
    Function.Injective (fkRectVertexSquareClass R) := by
  intro x y hxy
  have hmem : fkRectVertexSquarePoint R x -
      fkRectVertexSquarePoint R y ∈ fkRectSquareDeckLattice R :=
    QuotientAddGroup.eq_iff_sub_mem.mp hxy
  obtain ⟨u, hu⟩ :=
    (mem_fkRectSquareDeckLattice_iff R _).mp hmem
  have hpoint : fkRectVertexSquarePoint R x =
      fkRectVertexSquarePoint R y + fkRectSquareDeckTranslation R u := by
    rw [hu]
    apply Prod.ext <;> simp <;> ring
  have htilt := congrArg fkRectSquareUndevelopPoint hpoint
  rw [fkRectSquareUndevelopPoint_add_deck] at htilt
  simp only [fkRectVertexSquarePoint,
    fkRectSquareUndevelopPoint_developPoint] at htilt
  have hxInt := congrArg Prod.fst htilt
  have hyInt := congrArg Prod.snd htilt
  simp only [Prod.fst, Prod.snd] at hxInt hyInt
  letI : NeZero R.width := ⟨ne_of_gt R.width_pos⟩
  letI : NeZero R.height := ⟨ne_of_gt R.height_pos⟩
  have hxMod : ((x.1.val : Int) : ZMod R.width) =
      ((y.1.val : Int) : ZMod R.width) := by
    have h := congrArg (fun z : Int => (z : ZMod R.width)) hxInt
    simpa using h
  have hyMod : ((x.2.val : Int) : ZMod R.height) =
      ((y.2.val : Int) : ZMod R.height) := by
    have h := congrArg (fun z : Int => (z : ZMod R.height)) hyInt
    simpa using h
  have hx : x.1 = y.1 := by
    apply Fin.ext
    have h := congrArg ZMod.val hxMod
    simpa only [Int.cast_natCast, ZMod.val_natCast_of_lt x.1.isLt,
      ZMod.val_natCast_of_lt y.1.isLt] using h
  have hy : x.2 = y.2 := by
    apply Fin.ext
    have h := congrArg ZMod.val hyMod
    simpa only [Int.cast_natCast, ZMod.val_natCast_of_lt x.2.isLt,
      ZMod.val_natCast_of_lt y.2.isLt] using h
  exact Prod.ext hx hy


end
end StatMech.FrontierD
