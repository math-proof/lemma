/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/DartOrbit.lean -/

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
open SimpleGraph Function


namespace StatMech

namespace Lattice

theorem dartDir_ne_zero (e : Dart) : e.dir ≠ 0 := by
  intro h
  have := unitWt_dir e
  rw [h] at this
  simp [unitWt] at this


theorem rot90Fun_zero : rot90Fun (0 : Site 2) = 0 := by
  funext i; fin_cases i <;> simp [rot90Fun]


theorem rot90Fun_dartDir_ne_zero (e : Dart) : rot90Fun e.dir ≠ 0 := by
  intro h
  exact dartDir_ne_zero e (rot90Fun_injective (by rw [h, rot90Fun_zero]))


theorem neg_rot90Fun_dartDir_ne_zero (e : Dart) : (-rot90Fun e.dir : Site 2) ≠ 0 := by
  intro h
  apply rot90Fun_dartDir_ne_zero e
  have := congrArg Neg.neg h; rwa [neg_neg, neg_zero] at this


theorem rot90Fun_dartDir_ne_dartDir (e : Dart) : rot90Fun e.dir ≠ e.dir := by
  intro h
  have h2 : rot90Fun (rot90Fun e.dir) = e.dir := by rw [h, h]
  rw [rot90Fun_rot90Fun'] at h2
  apply dartDir_ne_zero e
  funext i; have hi := congrFun h2 i
  simp only [Pi.neg_apply, Pi.zero_apply] at hi ⊢; omega


theorem neg_rot90Fun_dartDir_ne_dartDir (e : Dart) : -rot90Fun e.dir ≠ e.dir := by
  intro h
  have hr : rot90Fun e.dir = -e.dir := by
    have := congrArg Neg.neg h; rwa [neg_neg] at this
  have h2 : rot90Fun (rot90Fun e.dir) = rot90Fun (-e.dir) := congrArg rot90Fun hr
  rw [rot90Fun_rot90Fun', rot90Fun_neg, hr, neg_neg] at h2
  apply dartDir_ne_zero e
  funext i; have hi := congrFun h2 i
  simp only [Pi.neg_apply, Pi.zero_apply] at hi ⊢; omega


theorem dartNext_ne_self (K : Set (Site 2)) (e : Dart) (_he : IsBoundaryDart K e) :
    dartNext K e ≠ e := by
  classical
  by_cases hA : e.head + (-rot90Fun e.dir) ∈ K
  · 
    intro hcon
    have hdir : (dartNext K e).dir = rot90Fun e.dir := (dartNext_front_head K e hA).2
    rw [hcon] at hdir
    exact rot90Fun_dartDir_ne_dartDir e hdir.symm
  · by_cases hB : e.tail + (-rot90Fun e.dir) ∈ K
    · 
      intro hcon
      have ht : (dartNext K e).tail = e.tail + (-rot90Fun e.dir) :=
        dartNext_straight_tail K e hA hB
      rw [hcon] at ht
      apply neg_rot90Fun_dartDir_ne_zero e
      have h' : e.tail + (-rot90Fun e.dir) = e.tail + 0 := by rw [add_zero]; exact ht.symm
      exact add_left_cancel h'
    · 
      intro hcon
      have hdir : (dartNext K e).dir = -rot90Fun e.dir := dartNext_left_dir K e hA hB
      rw [hcon] at hdir
      exact neg_rot90Fun_dartDir_ne_dartDir e hdir.symm


theorem dartNext_consecutive (K : Set (Site 2)) (e : Dart) :
    ((dartNext K e).head = e.head) ∨
    ((dartNext K e).tail = e.tail + (-rot90Fun e.dir) ∧
     (dartNext K e).head = e.head + (-rot90Fun e.dir)) ∨
    ((dartNext K e).tail = e.tail) := by
  classical
  by_cases hA : e.head + (-rot90Fun e.dir) ∈ K
  · exact Or.inl (dartNext_front_head K e hA).1
  · by_cases hB : e.tail + (-rot90Fun e.dir) ∈ K
    · exact Or.inr (Or.inl ⟨dartNext_straight_tail K e hA hB, dartNext_straight_head K e hA hB⟩)
    · exact Or.inr (Or.inr (dartNext_left_tail K e hA hB))


end Lattice
end StatMech
