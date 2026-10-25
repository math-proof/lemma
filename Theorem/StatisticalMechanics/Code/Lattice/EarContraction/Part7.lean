/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EarContraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarRemoval.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Def.StatisticalMechanics.Code.Lattice.EarContraction.Part7
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem it1_1 : (dartNext unitCell)^[1] ucDart1 = ucDart2 := by
  rw [iterate_one]; exact dartNext_ucDart1

theorem it1_2 : (dartNext unitCell)^[2] ucDart1 = ucDart3 := by
  rw [iterate_succ_apply', it1_1, dartNext_ucDart2]

theorem it1_3 : (dartNext unitCell)^[3] ucDart1 = ucDart0 := by
  rw [iterate_succ_apply', it1_2, dartNext_ucDart3]

theorem it1_4 : (dartNext unitCell)^[4] ucDart1 = ucDart1 := by
  rw [iterate_succ_apply', it1_3, dartNext_ucDart0]

theorem it2_1 : (dartNext unitCell)^[1] ucDart2 = ucDart3 := by
  rw [iterate_one]; exact dartNext_ucDart2

theorem it2_2 : (dartNext unitCell)^[2] ucDart2 = ucDart0 := by
  rw [iterate_succ_apply', it2_1, dartNext_ucDart3]

theorem it2_3 : (dartNext unitCell)^[3] ucDart2 = ucDart1 := by
  rw [iterate_succ_apply', it2_2, dartNext_ucDart0]

theorem it2_4 : (dartNext unitCell)^[4] ucDart2 = ucDart2 := by
  rw [iterate_succ_apply', it2_3, dartNext_ucDart1]

theorem it3_1 : (dartNext unitCell)^[1] ucDart3 = ucDart0 := by
  rw [iterate_one]; exact dartNext_ucDart3

theorem it3_2 : (dartNext unitCell)^[2] ucDart3 = ucDart1 := by
  rw [iterate_succ_apply', it3_1, dartNext_ucDart0]

theorem it3_3 : (dartNext unitCell)^[3] ucDart3 = ucDart2 := by
  rw [iterate_succ_apply', it3_2, dartNext_ucDart1]

theorem it3_4 : (dartNext unitCell)^[4] ucDart3 = ucDart3 := by
  rw [iterate_succ_apply', it3_3, dartNext_ucDart2]


theorem ucBase1_period4 : Function.IsPeriodicPt (dartNextSub unitCell) 4 ucBase1 := by
  unfold Function.IsPeriodicPt Function.IsFixedPt
  apply Subtype.ext; rw [dartNextSub_iterate_val]; exact it1_4

theorem ucBase1_notfix : ¬ Function.IsFixedPt (dartNextSub unitCell) ucBase1 := by
  intro h
  have h2 : dartNext unitCell ucDart1 = ucDart1 := by
    have := congrArg Subtype.val h; rwa [dartNextSub_val] at this
  rw [dartNext_ucDart1] at h2
  have hd := congrArg Dart.dir h2; rw [ucDart2_dir, ucDart1_dir] at hd
  have := congrFun hd 0; simp at this

theorem ucBase1_notper2 : ¬ Function.IsPeriodicPt (dartNextSub unitCell) 2 ucBase1 := by
  intro h
  have h2 : (dartNext unitCell)^[2] ucDart1 = ucDart1 := by
    have := congrArg Subtype.val h; rwa [dartNextSub_iterate_val] at this
  rw [it1_2] at h2
  have hd := congrArg Dart.dir h2; rw [ucDart3_dir, ucDart1_dir] at hd
  have := congrFun hd 1; simp at this

theorem ucBase1_orbitPeriod : dartOrbitPeriod unitCell ucBase1 = 4 := by
  unfold dartOrbitPeriod
  have hdvd : Function.minimalPeriod (dartNextSub unitCell) ucBase1 ∣ 4 :=
    Function.isPeriodicPt_iff_minimalPeriod_dvd.mp ucBase1_period4
  have hper := Function.isPeriodicPt_minimalPeriod (dartNextSub unitCell) ucBase1
  set m := Function.minimalPeriod (dartNextSub unitCell) ucBase1 with hm
  have hmem : m = 1 ∨ m = 2 ∨ m = 4 := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd; interval_cases m <;> omega
  rcases hmem with h | h | h
  · rw [h] at hper; rw [Function.IsPeriodicPt, iterate_one] at hper; exact absurd hper ucBase1_notfix
  · rw [h] at hper; exact absurd hper ucBase1_notper2
  · exact h

theorem ucBase2_period4 : Function.IsPeriodicPt (dartNextSub unitCell) 4 ucBase2 := by
  unfold Function.IsPeriodicPt Function.IsFixedPt
  apply Subtype.ext; rw [dartNextSub_iterate_val]; exact it2_4

theorem ucBase2_notfix : ¬ Function.IsFixedPt (dartNextSub unitCell) ucBase2 := by
  intro h
  have h2 : dartNext unitCell ucDart2 = ucDart2 := by
    have := congrArg Subtype.val h; rwa [dartNextSub_val] at this
  rw [dartNext_ucDart2] at h2
  have hd := congrArg Dart.dir h2; rw [ucDart3_dir, ucDart2_dir] at hd
  have := congrFun hd 0; simp at this

theorem ucBase2_notper2 : ¬ Function.IsPeriodicPt (dartNextSub unitCell) 2 ucBase2 := by
  intro h
  have h2 : (dartNext unitCell)^[2] ucDart2 = ucDart2 := by
    have := congrArg Subtype.val h; rwa [dartNextSub_iterate_val] at this
  rw [it2_2] at h2
  have hd := congrArg Dart.dir h2; rw [ucDart0_dir, ucDart2_dir] at hd
  have := congrFun hd 0; simp at this

theorem ucBase2_orbitPeriod : dartOrbitPeriod unitCell ucBase2 = 4 := by
  unfold dartOrbitPeriod
  have hdvd : Function.minimalPeriod (dartNextSub unitCell) ucBase2 ∣ 4 :=
    Function.isPeriodicPt_iff_minimalPeriod_dvd.mp ucBase2_period4
  have hper := Function.isPeriodicPt_minimalPeriod (dartNextSub unitCell) ucBase2
  set m := Function.minimalPeriod (dartNextSub unitCell) ucBase2 with hm
  have hmem : m = 1 ∨ m = 2 ∨ m = 4 := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd; interval_cases m <;> omega
  rcases hmem with h | h | h
  · rw [h] at hper; rw [Function.IsPeriodicPt, iterate_one] at hper; exact absurd hper ucBase2_notfix
  · rw [h] at hper; exact absurd hper ucBase2_notper2
  · exact h

theorem ucBase3_period4 : Function.IsPeriodicPt (dartNextSub unitCell) 4 ucBase3 := by
  unfold Function.IsPeriodicPt Function.IsFixedPt
  apply Subtype.ext; rw [dartNextSub_iterate_val]; exact it3_4

theorem ucBase3_notfix : ¬ Function.IsFixedPt (dartNextSub unitCell) ucBase3 := by
  intro h
  have h2 : dartNext unitCell ucDart3 = ucDart3 := by
    have := congrArg Subtype.val h; rwa [dartNextSub_val] at this
  rw [dartNext_ucDart3] at h2
  have hd := congrArg Dart.dir h2; rw [ucDart0_dir, ucDart3_dir] at hd
  have := congrFun hd 0; simp at this

theorem ucBase3_notper2 : ¬ Function.IsPeriodicPt (dartNextSub unitCell) 2 ucBase3 := by
  intro h
  have h2 : (dartNext unitCell)^[2] ucDart3 = ucDart3 := by
    have := congrArg Subtype.val h; rwa [dartNextSub_iterate_val] at this
  rw [it3_2] at h2
  have hd := congrArg Dart.dir h2; rw [ucDart1_dir, ucDart3_dir] at hd
  have := congrFun hd 1; simp at this

theorem ucBase3_orbitPeriod : dartOrbitPeriod unitCell ucBase3 = 4 := by
  unfold dartOrbitPeriod
  have hdvd : Function.minimalPeriod (dartNextSub unitCell) ucBase3 ∣ 4 :=
    Function.isPeriodicPt_iff_minimalPeriod_dvd.mp ucBase3_period4
  have hper := Function.isPeriodicPt_minimalPeriod (dartNextSub unitCell) ucBase3
  set m := Function.minimalPeriod (dartNextSub unitCell) ucBase3 with hm
  have hmem : m = 1 ∨ m = 2 ∨ m = 4 := by
    have hle := Nat.le_of_dvd (by norm_num) hdvd; interval_cases m <;> omega
  rcases hmem with h | h | h
  · rw [h] at hper; rw [Function.IsPeriodicPt, iterate_one] at hper; exact absurd hper ucBase3_notfix
  · rw [h] at hper; exact absurd hper ucBase3_notper2
  · exact h


theorem ucBase1_totalTurnZ : totalTurnZ unitCell ucDart1 4 = -4 := by
  apply totalTurnZ_four_of_all_left
  · exact ucDart1_turnZ
  · rw [dartNext_ucDart1]; exact ucDart2_turnZ
  · rw [it1_2]; exact ucDart3_turnZ
  · rw [it1_3]; exact ucDart0_turnZ

theorem ucBase2_totalTurnZ : totalTurnZ unitCell ucDart2 4 = -4 := by
  apply totalTurnZ_four_of_all_left
  · exact ucDart2_turnZ
  · rw [dartNext_ucDart2]; exact ucDart3_turnZ
  · rw [it2_2]; exact ucDart0_turnZ
  · rw [it2_3]; exact ucDart1_turnZ

theorem ucBase3_totalTurnZ : totalTurnZ unitCell ucDart3 4 = -4 := by
  apply totalTurnZ_four_of_all_left
  · exact ucDart3_turnZ
  · rw [dartNext_ucDart3]; exact ucDart0_turnZ
  · rw [it3_2]; exact ucDart1_turnZ
  · rw [it3_3]; exact ucDart2_turnZ


theorem unitCell_cornerBalance (a : {e : Dart // IsBoundaryDart unitCell e})
    (ha : a.1 = ucDart0 ∨ a.1 = ucDart1 ∨ a.1 = ucDart2 ∨ a.1 = ucDart3) :
    cornerBalance unitCell a = -4 := by
  rw [cornerBalance_eq_totalTurnZ]
  rcases ha with h | h | h | h
  · rw [h]
    have : dartOrbitPeriod unitCell a = 4 := by
      have hb : a = ucBase := Subtype.ext h
      rw [hb]; exact unitCell_orbitPeriod_eq_four
    rw [this]; exact unitCell_totalTurnZ_four
  · rw [h]
    have : dartOrbitPeriod unitCell a = 4 := by
      have hb : a = ucBase1 := Subtype.ext h
      rw [hb]; exact ucBase1_orbitPeriod
    rw [this]; exact ucBase1_totalTurnZ
  · rw [h]
    have : dartOrbitPeriod unitCell a = 4 := by
      have hb : a = ucBase2 := Subtype.ext h
      rw [hb]; exact ucBase2_orbitPeriod
    rw [this]; exact ucBase2_totalTurnZ
  · rw [h]
    have : dartOrbitPeriod unitCell a = 4 := by
      have hb : a = ucBase3 := Subtype.ext h
      rw [hb]; exact ucBase3_orbitPeriod
    rw [this]; exact ucBase3_totalTurnZ


theorem transSet_unitCell (v : Site 2) : transSet v unitCell = {v} := by
  unfold transSet unitCell
  rw [Set.image_singleton]
  congr 1
  funext i; fin_cases i <;> simp


theorem singleton_boundaryDart_tail (v : Site 2) (e : Dart)
    (he : IsBoundaryDart ({v} : Set (Site 2)) e) : e.tail = v := he.1


theorem singleton_boundaryDart_dir (v : Site 2) (e : Dart)
    (_he : IsBoundaryDart ({v} : Set (Site 2)) e) :
    e.dir = ![1, 0] ∨ e.dir = ![-1, 0] ∨ e.dir = ![0, 1] ∨ e.dir = ![0, -1] := by
  have hadj := e.adj
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  have key : ((e.dir 0).natAbs = 1 ∧ (e.dir 1).natAbs = 0) ∨
             ((e.dir 0).natAbs = 0 ∧ (e.dir 1).natAbs = 1) := by
    have hd : e.dir = e.head - e.tail := rfl
    rw [hd]; simp only [Pi.sub_apply]; omega
  rcases key with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · rcases Int.natAbs_eq_iff.mp h0 with h | h
    · left; funext i; fin_cases i <;> simp_all [Dart.dir]
    · right; left; funext i; fin_cases i <;> simp_all [Dart.dir]
  · rcases Int.natAbs_eq_iff.mp h1 with h | h
    · right; right; left; funext i; fin_cases i <;> simp_all [Dart.dir]
    · right; right; right; funext i; fin_cases i <;> simp_all [Dart.dir]


theorem singleton_boundaryDart_eq_transDart (v : Site 2) (e : Dart)
    (he : IsBoundaryDart ({v} : Set (Site 2)) e) :
    (e = transDart v ucDart0 ∧ e.dir = ![1, 0]) ∨
    (e = transDart v ucDart2 ∧ e.dir = ![-1, 0]) ∨
    (e = transDart v ucDart3 ∧ e.dir = ![0, 1]) ∨
    (e = transDart v ucDart1 ∧ e.dir = ![0, -1]) := by
  have htail : e.tail = v := he.1
  rcases singleton_boundaryDart_dir v e he with h | h | h | h
  · left; refine ⟨?_, h⟩
    apply dart_eq_of_tail_dir
    · rw [htail, transDart_tail, ucDart0_tail]; funext i; fin_cases i <;> simp
    · rw [h, transDart_dir, ucDart0_dir]
  · right; left; refine ⟨?_, h⟩
    apply dart_eq_of_tail_dir
    · rw [htail, transDart_tail, ucDart2_tail]; funext i; fin_cases i <;> simp
    · rw [h, transDart_dir, ucDart2_dir]
  · right; right; left; refine ⟨?_, h⟩
    apply dart_eq_of_tail_dir
    · rw [htail, transDart_tail, ucDart3_tail]; funext i; fin_cases i <;> simp
    · rw [h, transDart_dir, ucDart3_dir]
  · right; right; right; refine ⟨?_, h⟩
    apply dart_eq_of_tail_dir
    · rw [htail, transDart_tail, ucDart1_tail]; funext i; fin_cases i <;> simp
    · rw [h, transDart_dir, ucDart1_dir]


theorem cornerBalance_congr (K K' : Set (Site 2)) (hKK : K = K')
    (a : {e : Dart // IsBoundaryDart K e}) (a' : {e : Dart // IsBoundaryDart K' e})
    (ha : a.1 = a'.1) : cornerBalance K a = cornerBalance K' a' := by
  subst hKK
  rw [Subtype.ext ha]


theorem singleton_cornerBalance_reduce (v : Site 2)
    (a : {e : Dart // IsBoundaryDart ({v} : Set (Site 2)) e})
    (b : {e : Dart // IsBoundaryDart unitCell e}) (he : a.1 = transDart v b.1) :
    cornerBalance ({v} : Set (Site 2)) a = cornerBalance unitCell b := by
  have hset : ({v} : Set (Site 2)) = transSet v unitCell := (transSet_unitCell v).symm
  have hstep : cornerBalance ({v} : Set (Site 2)) a
      = cornerBalance (transSet v unitCell) (transSub unitCell v b) := by
    apply cornerBalance_congr ({v} : Set (Site 2)) (transSet v unitCell) hset
    rw [he, transSub_val]
  rw [hstep, cornerBalance_trans]


theorem singleton_cornerBalance (v : Site 2)
    (a : {e : Dart // IsBoundaryDart ({v} : Set (Site 2)) e}) :
    cornerBalance ({v} : Set (Site 2)) a = -4 := by
  rcases singleton_boundaryDart_eq_transDart v a.1 a.2 with
    ⟨he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩ | ⟨he, _⟩
  · rw [singleton_cornerBalance_reduce v a ucBase he]
    exact unitCell_cornerBalance ucBase (Or.inl rfl)
  · rw [singleton_cornerBalance_reduce v a ucBase2 he]
    exact unitCell_cornerBalance ucBase2 (Or.inr (Or.inr (Or.inl rfl)))
  · rw [singleton_cornerBalance_reduce v a ucBase3 he]
    exact unitCell_cornerBalance ucBase3 (Or.inr (Or.inr (Or.inr rfl)))
  · rw [singleton_cornerBalance_reduce v a ucBase1 he]
    exact unitCell_cornerBalance ucBase1 (Or.inr (Or.inl rfl))


end Lattice
end StatMech
