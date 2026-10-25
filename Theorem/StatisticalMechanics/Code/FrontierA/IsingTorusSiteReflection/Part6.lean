/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSpinReflection.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusSiteReflection.Part5
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}

theorem isingTorusDirichlet_siteReflectField
    (i : Fin d) (u : IsingDyadicTorus d k → Real) :
    isingTorusDirichlet (isingTorusSiteReflectField i u) =
      isingTorusDirichlet u := by
  unfold isingTorusDirichlet isingTorusDirichletBilinear
  calc
    (∑ x : IsingDyadicTorus d k, ∑ j : Fin d,
        (isingTorusSiteReflectField i u x -
          isingTorusSiteReflectField i u (x + isingTorusStep j)) *
        (isingTorusSiteReflectField i u x -
          isingTorusSiteReflectField i u (x + isingTorusStep j))) =
      ∑ j : Fin d, ∑ x : IsingDyadicTorus d k,
        (isingTorusSiteReflectField i u x -
          isingTorusSiteReflectField i u (x + isingTorusStep j)) *
        (isingTorusSiteReflectField i u x -
          isingTorusSiteReflectField i u (x + isingTorusStep j)) :=
        Finset.sum_comm
    _ = ∑ j : Fin d, ∑ x : IsingDyadicTorus d k,
        (u x - u (x + isingTorusStep j)) *
          (u x - u (x + isingTorusStep j)) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i
      · subst j
        let e : IsingDyadicTorus d k → IsingDyadicTorus d k := fun x =>
          isingTorusSiteReflect i x - isingTorusStep i
        have hinv : Function.Involutive
            (isingTorusSiteReflect (k := k) i) :=
          fun x => isingTorusSiteReflect_involutive i x
        have hreflect : Function.Bijective
            (isingTorusSiteReflect (k := k) i) := hinv.bijective
        have he : Function.Bijective e :=
          (Equiv.subRight (isingTorusStep (k := k) i)).bijective.comp
            hreflect
        calc
          (∑ x,
              (isingTorusSiteReflectField i u x -
                isingTorusSiteReflectField i u (x + isingTorusStep i)) *
              (isingTorusSiteReflectField i u x -
                isingTorusSiteReflectField i u (x + isingTorusStep i))) =
            ∑ x, (u (e x + isingTorusStep i) - u (e x)) *
              (u (e x + isingTorusStep i) - u (e x)) := by
                apply Finset.sum_congr rfl
                intro x _
                dsimp only [e, isingTorusSiteReflectField]
                rw [isingTorusSiteReflect_add_step_same]
                ring
          _ = ∑ x, (u (x + isingTorusStep i) - u x) *
              (u (x + isingTorusStep i) - u x) :=
            he.sum_comp (fun y : IsingDyadicTorus d k =>
              (u (y + isingTorusStep i) - u y) *
                (u (y + isingTorusStep i) - u y))
          _ = ∑ x, (u x - u (x + isingTorusStep i)) *
              (u x - u (x + isingTorusStep i)) := by
                apply Finset.sum_congr rfl
                intro x _
                ring
      · have hinv : Function.Involutive
            (isingTorusSiteReflect (k := k) i) :=
          fun x => isingTorusSiteReflect_involutive i x
        have hreflect : Function.Bijective
            (isingTorusSiteReflect (k := k) i) := hinv.bijective
        calc
          (∑ x,
              (isingTorusSiteReflectField i u x -
                isingTorusSiteReflectField i u (x + isingTorusStep j)) *
              (isingTorusSiteReflectField i u x -
                isingTorusSiteReflectField i u (x + isingTorusStep j))) =
            ∑ x, (u (isingTorusSiteReflect i x) -
              u (isingTorusSiteReflect i x + isingTorusStep j)) *
              (u (isingTorusSiteReflect i x) -
                u (isingTorusSiteReflect i x + isingTorusStep j)) := by
                apply Finset.sum_congr rfl
                intro x _
                dsimp only [isingTorusSiteReflectField]
                rw [isingTorusSiteReflect_add_step_of_ne i j hji]
          _ = ∑ x, (u x - u (x + isingTorusStep j)) *
              (u x - u (x + isingTorusStep j)) :=
            hreflect.sum_comp (fun y : IsingDyadicTorus d k =>
              (u y - u (y + isingTorusStep j)) *
                (u y - u (y + isingTorusStep j)))
    _ = ∑ x : IsingDyadicTorus d k, ∑ j : Fin d,
        (u x - u (x + isingTorusStep j)) *
          (u x - u (x + isingTorusStep j)) := Finset.sum_comm

theorem isingTorusDirichletBilinear_siteReflectField
    (i : Fin d) (u v : IsingDyadicTorus d k → Real) :
    isingTorusDirichletBilinear
        (isingTorusSiteReflectField i u)
        (isingTorusSiteReflectField i v) =
      isingTorusDirichletBilinear u v := by
  have hadd := isingTorusDirichlet_add u v
  have haddR := isingTorusDirichlet_add
    (isingTorusSiteReflectField i u) (isingTorusSiteReflectField i v)
  have hrefAdd : isingTorusSiteReflectField i (u + v) =
      isingTorusSiteReflectField i u +
        isingTorusSiteReflectField i v := rfl
  rw [← hrefAdd,
    isingTorusDirichlet_siteReflectField,
    isingTorusDirichlet_siteReflectField,
    isingTorusDirichlet_siteReflectField] at haddR
  linarith


theorem isingTorusSiteReflect_strictLower_iff_upper
    (i : Fin d) (x : IsingDyadicTorus d k) :
    isingTorusInStrictLower i (isingTorusSiteReflect i x) ↔
      2 ^ (k + 1) < (x i).val := by
  unfold isingTorusInStrictLower
  rw [isingTorusSiteReflect_apply_same]
  by_cases hx0 : x i = 0
  · simp [hx0]
  · rw [ZMod.neg_val, if_neg hx0]
    have hxlt := (x i).val_lt
    have hside := isingTorus_side_eq_two_half (k := k)
    constructor <;> intro h <;> omega

theorem isingTorus_no_edge_meets_both_strict_halves
    (i j : Fin d) (x : IsingDyadicTorus d k) :
    ¬ ((isingTorusInStrictLower i x ∨
          isingTorusInStrictLower i (x + isingTorusStep j)) ∧
        (isingTorusInStrictLower i (isingTorusSiteReflect i x) ∨
          isingTorusInStrictLower i
            (isingTorusSiteReflect i (x + isingTorusStep j)))) := by
  rw [isingTorusSiteReflect_strictLower_iff_upper,
    isingTorusSiteReflect_strictLower_iff_upper]
  simp only [isingTorusInStrictLower]
  by_cases hji : j = i
  · subst j
    have hone : (1 : ZMod (2 ^ (k + 2))).val = 1 := by
      have hlt : 1 < 2 ^ (k + 2) := by
        have hp : 0 < 2 ^ (k + 1) := pow_pos (by omega) _
        have hside := isingTorus_side_eq_two_half (k := k)
        omega
      letI : Fact (1 < 2 ^ (k + 2)) := ⟨hlt⟩
      exact ZMod.val_one (2 ^ (k + 2))
    have hycoord : (x + isingTorusStep (k := k) i) i = x i + 1 := by
      simp [Pi.add_apply, isingTorusStep_apply_same]
    rw [hycoord]
    by_cases hsum : (x i).val + (1 : ZMod (2 ^ (k + 2))).val <
        2 ^ (k + 2)
    · rw [ZMod.val_add_of_lt hsum, hone]
      rintro ⟨hl, hu⟩
      rcases hl with hl | hl <;> rcases hu with hu | hu <;>
        omega
    · have hle : 2 ^ (k + 2) ≤
          (x i).val + (1 : ZMod (2 ^ (k + 2))).val := by omega
      rw [ZMod.val_add_of_le hle, hone]
      have hxlt := (x i).val_lt
      rintro ⟨hl, hu⟩
      rcases hl with hl | hl <;> rcases hu with hu | hu <;>
        omega
  · have hcoord : (x + isingTorusStep (k := k) j) i = x i := by
      rw [Pi.add_apply, isingTorusStep_apply_of_ne j i (Ne.symm hji),
        add_zero]
    rw [hcoord]
    rintro ⟨hl, hu⟩
    rcases hl with hl | hl <;> omega

end StatMech.FrontierA
