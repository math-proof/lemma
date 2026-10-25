/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSpinReflection.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusSiteReflection.Part3
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}

@[simp] theorem isingTorusSiteSplit_glue
    (i : Fin d)
    (boundary : ConfigSpace (IsingTorusSitePlane (k := k) i))
    (lower upper : ConfigSpace (IsingTorusStrictLower (k := k) i)) :
    isingTorusSiteSplit i (isingTorusSiteGlue i boundary lower upper) =
      (boundary, (lower, upper)) := by
  apply Prod.ext
  · funext x
    simp [isingTorusSiteSplit, isingTorusSiteGlue, x.2]
  · apply Prod.ext
    · funext x
      have hnp : ¬ isingTorusOnSitePlane i x.1 := by
        intro hp
        rcases x.2 with ⟨hx0, hxhalf⟩
        rcases hp with hp | hp <;> omega
      simp [isingTorusSiteSplit, isingTorusSiteGlue, hnp, x.2]
    · funext x
      have hnp : ¬ isingTorusOnSitePlane i x.1 := by
        intro hp
        rcases x.2 with ⟨hx0, hxhalf⟩
        rcases hp with hp | hp <;> omega
      have hnpR : ¬ isingTorusOnSitePlane i
          (isingTorusSiteReflect i x.1) :=
        isingTorusSiteReflect_not_plane i hnp
      have hlR : ¬ isingTorusInStrictLower i
          (isingTorusSiteReflect i x.1) := by
        intro hl
        have hval := hl.2
        have hxi0 : x.1 i ≠ 0 :=
          (ZMod.val_ne_zero (x.1 i)).mp (ne_of_gt x.2.1)
        rw [isingTorusSiteReflect_apply_same, ZMod.neg_val,
          if_neg hxi0] at hval
        have hxlt := (x.1 i).val_lt
        have hxhalf := x.2.2
        have hside := isingTorus_side_eq_two_half (k := k)
        omega
      simp [isingTorusSiteSplit, isingTorusSiteGlue, hnpR, hlR]

@[simp] theorem isingTorusSiteGlue_split
    (i : Fin d) (sigma : ConfigSpace (IsingDyadicTorus d k)) :
    isingTorusSiteGlue i (isingTorusSiteSplit i sigma).1
      (isingTorusSiteSplit i sigma).2.1
      (isingTorusSiteSplit i sigma).2.2 = sigma := by
  funext x
  by_cases hp : isingTorusOnSitePlane i x
  · simp [isingTorusSiteGlue, isingTorusSiteSplit, hp]
  · by_cases hl : isingTorusInStrictLower i x
    · simp [isingTorusSiteGlue, isingTorusSiteSplit, hp, hl]
    · simp [isingTorusSiteGlue, isingTorusSiteSplit, hp, hl]


end StatMech.FrontierA
