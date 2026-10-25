/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc38sharp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc37hdom.Part4
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.FieldGhostDict


section Abstract

variable {ι W : Type*} [DecidableEq ι] [DecidableEq W] [Fintype W] [Fintype ι]


theorem gc38_comp_sources_even (ends : ι → Sym2 W) (K : Finset ι)
    (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag) (u : W) :
    Even (#((RandomCurrent.compOf ends K u).filter (fun z => z ∈ RandomCurrent.sources ends K))) := by
  have h1 : Even (#((RandomCurrent.compOf ends K u).filter (fun z => Odd (RandomCurrent.degK ends K z)))) :=
    (RandomCurrent.even_sum_iff_even_count _ _).1 (RandomCurrent.sum_deg_comp_even ends K hnd u)
  have hset : (RandomCurrent.compOf ends K u).filter (fun z => z ∈ RandomCurrent.sources ends K)
      = (RandomCurrent.compOf ends K u).filter (fun z => Odd (RandomCurrent.degK ends K z)) := by
    apply Finset.filter_congr; intro z _; simp [RandomCurrent.mem_sources]
  rw [hset]; exact h1


theorem gc38_comp_source_count (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    (hdist : o ≠ x ∧ o ≠ y ∧ o ≠ g ∧ x ≠ y ∧ x ≠ g ∧ y ≠ g)
    (hsrc : RandomCurrent.sources ends K = {o, x, y, g}) (u : W) :
    #((RandomCurrent.compOf ends K u).filter (fun z => z ∈ RandomCurrent.sources ends K))
      = (if RandomCurrent.connK ends K u o then 1 else 0) + (if RandomCurrent.connK ends K u x then 1 else 0)
        + (if RandomCurrent.connK ends K u y then 1 else 0) + (if RandomCurrent.connK ends K u g then 1 else 0) := by
  obtain ⟨hox, hoy, hog, hxy, hxg, hyg⟩ := hdist
  rw [show (RandomCurrent.compOf ends K u).filter (fun z => z ∈ RandomCurrent.sources ends K)
        = (({o, x, y, g} : Finset W)).filter (fun z => RandomCurrent.connK ends K u z) from ?_]
  · rw [Finset.card_filter, Finset.sum_insert (by simp [hox, hoy, hog]),
      Finset.sum_insert (by simp [hxy, hxg]), Finset.sum_insert (by simp [hyg]),
      Finset.sum_singleton]
    ring
  · ext z; simp only [Finset.mem_filter, RandomCurrent.mem_compOf, hsrc]; tauto


theorem gc38_disconn_triple_identity (ends : ι → Sym2 W) (K : Finset ι)
    (hnd : ∀ i ∈ K, ¬ (ends i).IsDiag) {o x y g : W}
    (hdist : o ≠ x ∧ o ≠ y ∧ o ≠ g ∧ x ≠ y ∧ x ≠ g ∧ y ≠ g)
    (hsrc : RandomCurrent.sources ends K = {o, x, y, g}) :
    (if ¬ RandomCurrent.connK ends K x y then (1 : ℝ) else 0)
      + (if ¬ RandomCurrent.connK ends K y g then 1 else 0)
      + (if ¬ RandomCurrent.connK ends K x g then 1 else 0)
      = 2 * (if ¬ (RandomCurrent.connK ends K o x ∧ RandomCurrent.connK ends K o y ∧ RandomCurrent.connK ends K o g) then 1 else 0) := by
  obtain ⟨hox_, hoy_, hog_, hxy_, hxg_, hyg_⟩ := hdist
  have po := gc38_comp_sources_even ends K hnd o
  have px := gc38_comp_sources_even ends K hnd x
  have py := gc38_comp_sources_even ends K hnd y
  rw [gc38_comp_source_count ends K ⟨hox_, hoy_, hog_, hxy_, hxg_, hyg_⟩ hsrc o] at po
  rw [gc38_comp_source_count ends K ⟨hox_, hoy_, hog_, hxy_, hxg_, hyg_⟩ hsrc x] at px
  rw [gc38_comp_source_count ends K ⟨hox_, hoy_, hog_, hxy_, hxg_, hyg_⟩ hsrc y] at py
  have coo : RandomCurrent.connK ends K o o := Relation.ReflTransGen.refl
  have cxx : RandomCurrent.connK ends K x x := Relation.ReflTransGen.refl
  have cyy : RandomCurrent.connK ends K y y := Relation.ReflTransGen.refl
  have link : ∀ a b, RandomCurrent.connK ends K o a → RandomCurrent.connK ends K o b → RandomCurrent.connK ends K a b :=
    fun a b h1 h2 => Relation.ReflTransGen.trans (RandomCurrent.connK_symm ends K h1) h2
  have nolink : ∀ a b, RandomCurrent.connK ends K o a → ¬ RandomCurrent.connK ends K o b → ¬ RandomCurrent.connK ends K a b :=
    fun a b h1 hnb hab => hnb (Relation.ReflTransGen.trans h1 hab)
  have csym : ∀ a b : W, RandomCurrent.connK ends K a b ↔ RandomCurrent.connK ends K b a :=
    fun a b => ⟨RandomCurrent.connK_symm ends K, RandomCurrent.connK_symm ends K⟩
  by_cases hoxc : RandomCurrent.connK ends K o x <;> by_cases hoyc : RandomCurrent.connK ends K o y <;>
    by_cases hogc : RandomCurrent.connK ends K o g <;>
    simp only [hoxc, hoyc, hogc, coo, cxx, cyy, if_true, if_false, and_true,
      not_false_iff, mul_one, csym x o, csym y o, csym y x] at po px py ⊢
  all_goals try (exfalso; revert po; decide)
  · 
    rw [if_neg (not_not.mpr (link x y hoxc hoyc)), if_neg (not_not.mpr (link y g hoyc hogc)),
      if_neg (not_not.mpr (link x g hoxc hogc))]
    norm_num
  · 
    have hxy_dis : ¬ RandomCurrent.connK ends K x y := nolink x y hoxc hoyc
    have hxg_dis : ¬ RandomCurrent.connK ends K x g := nolink x g hoxc hogc
    simp only [hxy_dis, if_false] at py
    have hyg : RandomCurrent.connK ends K y g := by
      revert py; by_cases h : RandomCurrent.connK ends K y g <;> simp [h]
    rw [if_pos hxy_dis, if_neg (not_not.mpr hyg), if_pos hxg_dis]
    norm_num
  · 
    have hyx_dis : ¬ RandomCurrent.connK ends K y x := nolink y x hoyc hoxc
    have hxy_dis : ¬ RandomCurrent.connK ends K x y := fun h => hyx_dis (RandomCurrent.connK_symm ends K h)
    have hyg_dis : ¬ RandomCurrent.connK ends K y g := nolink y g hoyc hogc
    simp only [hxy_dis, if_false] at px
    have hxg : RandomCurrent.connK ends K x g := by
      revert px; by_cases h : RandomCurrent.connK ends K x g <;> simp [h]
    rw [if_pos hxy_dis, if_pos hyg_dis, if_neg (not_not.mpr hxg)]
    norm_num
  · 
    have hgx_dis : ¬ RandomCurrent.connK ends K g x := nolink g x hogc hoxc
    have hxg_dis : ¬ RandomCurrent.connK ends K x g := fun h => hgx_dis (RandomCurrent.connK_symm ends K h)
    have hgy_dis : ¬ RandomCurrent.connK ends K g y := nolink g y hogc hoyc
    have hyg_dis : ¬ RandomCurrent.connK ends K y g := fun h => hgy_dis (RandomCurrent.connK_symm ends K h)
    simp only [hxg_dis, if_false] at px
    have hxy : RandomCurrent.connK ends K x y := by
      revert px; by_cases h : RandomCurrent.connK ends K x y <;> simp [h]
    rw [if_neg (not_not.mpr hxy), if_pos hyg_dis, if_pos hxg_dis]
    norm_num

end Abstract
end StatMech.Walls
