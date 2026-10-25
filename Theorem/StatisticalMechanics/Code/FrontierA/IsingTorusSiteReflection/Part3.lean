/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSpinReflection.Part2
import Instance.StatisticalMechanics.Code.FrontierA.IsingTorusSiteReflection
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}

theorem isingTorusSiteReflect_fixed
    (i : Fin d) {x : IsingDyadicTorus d k}
    (hx : isingTorusOnSitePlane i x) :
    isingTorusSiteReflect i x = x := by
  funext j
  by_cases hji : j = i
  · subst j
    rw [isingTorusSiteReflect_apply_same]
    apply (ZMod.neg_eq_self_iff (x i)).2
    rcases hx with hx | hx
    · left
      exact (ZMod.val_eq_zero (x i)).mp hx
    · right
      rw [hx, isingTorus_side_eq_two_half]
  · exact isingTorusSiteReflect_apply_of_ne i j hji x

theorem isingTorusSiteReflect_strictLower_of_upper
    (i : Fin d) {x : IsingDyadicTorus d k}
    (hplane : ¬ isingTorusOnSitePlane i x)
    (hlower : ¬ isingTorusInStrictLower i x) :
    isingTorusInStrictLower i (isingTorusSiteReflect i x) := by
  have hx0 : (x i).val ≠ 0 := fun h => hplane (Or.inl h)
  have hxhalf : (x i).val ≠ 2 ^ (k + 1) :=
    fun h => hplane (Or.inr h)
  have hxge : 2 ^ (k + 1) < (x i).val := by
    unfold isingTorusInStrictLower at hlower
    push Not at hlower
    have hpos : 0 < (x i).val := Nat.pos_of_ne_zero hx0
    have hge := hlower hpos
    omega
  have hxi0 : x i ≠ 0 := (ZMod.val_ne_zero (x i)).mp hx0
  unfold isingTorusInStrictLower
  rw [isingTorusSiteReflect_apply_same, ZMod.neg_val,
    if_neg hxi0]
  have hxlt := (x i).val_lt
  have hside := isingTorus_side_eq_two_half (k := k)
  omega

theorem isingTorusSiteReflect_not_plane
    (i : Fin d) {x : IsingDyadicTorus d k}
    (hx : ¬ isingTorusOnSitePlane i x) :
    ¬ isingTorusOnSitePlane i (isingTorusSiteReflect i x) := by
  intro hr
  have heq : x = isingTorusSiteReflect i x := by
    simpa using isingTorusSiteReflect_fixed i hr
  apply hx
  rw [heq]
  exact hr

end StatMech.FrontierA
