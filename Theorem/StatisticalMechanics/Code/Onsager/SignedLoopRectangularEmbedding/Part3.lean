/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularDualPath.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleHolonomy.Part5
import Def.StatisticalMechanics.Code.Onsager.SignedLoopRectangularEmbedding.Part3
open Set SimpleGraph


namespace StatMech.Onsager

open StatMech.FrontierA

noncomputable section

theorem ons_rectDualIntPoint_snd_eq_add_step {M N : Nat}
    (dart : (ons_rectDualGraph M N).Dart) :
    ons_rectDualIntPoint dart.snd =
      ons_rectDualIntPoint dart.fst +
        triangularIntStep (ons_rectDualDartDirection dart) := by
  have hadj : ons_rectDualAdj M N dart.fst dart.snd := dart.adj
  rcases hadj with ⟨hy, hx⟩ | ⟨hx, hy⟩
  · have hne : dart.fst.1.val ≠ dart.snd.1.val := by
      intro h
      simp [h] at hx
    by_cases hlt : dart.snd.1.val < dart.fst.1.val
    · have hval : dart.fst.1.val = dart.snd.1.val + 1 := by
        rw [Nat.dist_comm,
          Nat.dist_eq_sub_of_le (Nat.le_of_lt hlt)] at hx
        omega
      simp [ons_rectDualIntPoint, ons_rectDualDartDirection, hlt,
        triangularIntStep, hy, Prod.ext_iff]
      omega
    · have hlt' : dart.fst.1.val < dart.snd.1.val :=
        lt_of_le_of_ne (Nat.le_of_not_gt hlt) hne
      have hval : dart.snd.1.val = dart.fst.1.val + 1 := by
        rw [Nat.dist_eq_sub_of_le (Nat.le_of_lt hlt')] at hx
        omega
      simp [ons_rectDualIntPoint, ons_rectDualDartDirection, hlt, hlt',
        triangularIntStep, hy, Prod.ext_iff]
      omega
  · have hne : dart.fst.2.val ≠ dart.snd.2.val := by
      intro h
      simp [h] at hy
    have hxVal : dart.fst.1.val = dart.snd.1.val :=
      congrArg Fin.val hx
    by_cases hlt : dart.snd.2.val < dart.fst.2.val
    · have hval : dart.fst.2.val = dart.snd.2.val + 1 := by
        rw [Nat.dist_comm,
          Nat.dist_eq_sub_of_le (Nat.le_of_lt hlt)] at hy
        omega
      simp [ons_rectDualIntPoint, ons_rectDualDartDirection,
        hlt, triangularIntStep, hxVal, Prod.ext_iff]
      omega
    · have hlt' : dart.fst.2.val < dart.snd.2.val :=
        lt_of_le_of_ne (Nat.le_of_not_gt hlt) hne
      have hval : dart.snd.2.val = dart.fst.2.val + 1 := by
        rw [Nat.dist_eq_sub_of_le (Nat.le_of_lt hlt')] at hy
        omega
      simp [ons_rectDualIntPoint, ons_rectDualDartDirection,
        hlt, triangularIntStep, hxVal, Prod.ext_iff]
      omega


end
end StatMech.Onsager
