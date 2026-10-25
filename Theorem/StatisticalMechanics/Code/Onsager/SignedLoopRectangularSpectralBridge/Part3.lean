/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularSpectralBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularEmbedding.Part4
import Theorem.StatisticalMechanics.Code.Onsager.KWRectangleWeighted.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleTopology.Part2
import Def.StatisticalMechanics.Code.Onsager.SignedLoopRectangularSpectralBridge.Part3
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.FrontierA

noncomputable section

theorem ons_rectDualDartSlot_valid {M N : Nat}
    (dart : (ons_rectDualGraph M N).Dart) :
    ons_rectDartValid M N (ons_rectDualDartSlot dart) := by
  have hadj : ons_rectDualAdj M N dart.fst dart.snd := dart.adj
  rcases hadj with ⟨hy, hx⟩ | ⟨hx, hy⟩
  · have hne : dart.fst.1.val ≠ dart.snd.1.val := by
      intro h
      simp [h] at hx
    by_cases hleft : dart.snd.1.val < dart.fst.1.val
    · have hpos : 0 < dart.fst.1.val :=
        lt_of_le_of_lt (Nat.zero_le _) hleft
      simpa [ons_rectDualDartSlot, ons_rectDualDartDirection4,
        ons_rectDartValid, hleft] using hpos
    · have hright : dart.fst.1.val < dart.snd.1.val :=
        lt_of_le_of_ne (Nat.le_of_not_gt hleft) hne
      have hhead : dart.snd.1.val < M + 1 := dart.snd.1.isLt
      simp [ons_rectDualDartSlot, ons_rectDualDartDirection4,
        ons_rectDartValid, hleft, hright]
      rw [Nat.dist_eq_sub_of_le hright.le] at hx
      omega
  · have hxval : dart.fst.1.val = dart.snd.1.val :=
      congrArg Fin.val hx
    have hne : dart.fst.2.val ≠ dart.snd.2.val := by
      intro h
      simp [h] at hy
    have hnotleft : ¬dart.snd.1.val < dart.fst.1.val := by omega
    have hnotright : ¬dart.fst.1.val < dart.snd.1.val := by omega
    by_cases hdown : dart.snd.2.val < dart.fst.2.val
    · have hpos : 0 < dart.fst.2.val :=
        lt_of_le_of_lt (Nat.zero_le _) hdown
      simpa [ons_rectDualDartSlot, ons_rectDualDartDirection4,
        ons_rectDartValid, hnotleft, hnotright, hdown] using hpos
    · have hup : dart.fst.2.val < dart.snd.2.val :=
        lt_of_le_of_ne (Nat.le_of_not_gt hdown) hne
      have hhead : dart.snd.2.val < N + 1 := dart.snd.2.isLt
      simp [ons_rectDualDartSlot, ons_rectDualDartDirection4,
        ons_rectDartValid, hnotleft, hnotright,
        hdown]
      rw [Nat.dist_eq_sub_of_le hup.le] at hy
      omega

theorem ons_rectDualDartSlot_injective {M N : Nat} :
    Function.Injective
      (ons_rectDualDartSlot :
        (ons_rectDualGraph M N).Dart → ons_RectDart M N) := by
  intro dart next hslot
  have htailSlot := congrArg (fun slot : ons_RectDart M N ↦ slot.1) hslot
  have hdir := congrArg (fun slot : ons_RectDart M N ↦ slot.2) hslot
  have htail : dart.fst = next.fst :=
    ons_rectDualVertexSlot_injective (by
      simpa [ons_rectDualDartSlot] using htailSlot)
  have hdir' : ons_rectDualDartDirection4 dart =
      ons_rectDualDartDirection4 next := by
    simpa [ons_rectDualDartSlot] using hdir
  have hvec := ons_rectDual_dartVector_eq_kwRectilinearVector dart
  have hvec' := ons_rectDual_dartVector_eq_kwRectilinearVector next
  have hhead : dart.snd = next.snd := by
    apply ons_rectDualComplexPoint_injective
    rw [← sub_eq_zero]
    calc
      ons_rectDualComplexPoint dart.snd - ons_rectDualComplexPoint next.snd =
          (ons_rectDualComplexPoint dart.snd -
              ons_rectDualComplexPoint dart.fst) -
            (ons_rectDualComplexPoint next.snd -
              ons_rectDualComplexPoint next.fst) := by rw [htail]; ring
      _ = 0 := by rw [hvec, hvec', hdir']; ring
  apply SimpleGraph.Dart.ext
  exact Prod.ext htail hhead

theorem ons_rectDualDartSlot_surjective_valid {M N : Nat}
    (slot : ons_RectDart M N) (hslot : ons_rectDartValid M N slot) :
    ∃ dart : (ons_rectDualGraph M N).Dart,
      ons_rectDualDartSlot dart = slot := by
  rcases slot with ⟨⟨x, y⟩, direction⟩
  fin_cases direction
  · simp [ons_rectDartValid] at hslot
    have hxlt : x.val < M + 1 := ZMod.val_lt x
    let u : ons_RectDualVertex M N :=
      (⟨x.val, ZMod.val_lt x⟩, ⟨y.val, ZMod.val_lt y⟩)
    let v : ons_RectDualVertex M N :=
      (⟨x.val + 1, by omega⟩, ⟨y.val, ZMod.val_lt y⟩)
    have hadj : ons_rectDualAdj M N u v := by
      left
      refine ⟨rfl, ?_⟩
      simp [u, v, Nat.dist_eq_sub_of_le]
    let dart : (ons_rectDualGraph M N).Dart := ⟨(u, v), hadj⟩
    refine ⟨dart, ?_⟩
    apply Prod.ext
    · apply Prod.ext <;>
        simp [ons_rectDualDartSlot, ons_rectDualVertexSlot, dart, u]
    · simp [ons_rectDualDartSlot, ons_rectDualDartDirection4, dart, u, v]
  · simp [ons_rectDartValid] at hslot
    let u : ons_RectDualVertex M N :=
      (⟨x.val, ZMod.val_lt x⟩, ⟨y.val, ZMod.val_lt y⟩)
    let v : ons_RectDualVertex M N :=
      (⟨x.val, ZMod.val_lt x⟩, ⟨y.val + 1, by omega⟩)
    have hadj : ons_rectDualAdj M N u v := by
      right
      refine ⟨rfl, ?_⟩
      simp [u, v, Nat.dist_eq_sub_of_le]
    let dart : (ons_rectDualGraph M N).Dart := ⟨(u, v), hadj⟩
    refine ⟨dart, ?_⟩
    apply Prod.ext
    · apply Prod.ext <;>
        simp [ons_rectDualDartSlot, ons_rectDualVertexSlot, dart, u]
    · simp [ons_rectDualDartSlot, ons_rectDualDartDirection4, dart, u, v]
  · simp [ons_rectDartValid] at hslot
    have hxlt : x.val < M + 1 := ZMod.val_lt x
    have hxpos : 0 < x.val := by
      exact Nat.pos_of_ne_zero (fun h ↦ hslot ((ZMod.val_eq_zero x).mp h))
    let u : ons_RectDualVertex M N :=
      (⟨x.val, ZMod.val_lt x⟩, ⟨y.val, ZMod.val_lt y⟩)
    let v : ons_RectDualVertex M N :=
      (⟨x.val - 1, by omega⟩, ⟨y.val, ZMod.val_lt y⟩)
    have hadj : ons_rectDualAdj M N u v := by
      left
      refine ⟨rfl, ?_⟩
      change Nat.dist x.val (x.val - 1) = 1
      rw [Nat.dist_comm,
        Nat.dist_eq_sub_of_le (Nat.sub_le _ _)]
      omega
    let dart : (ons_rectDualGraph M N).Dart := ⟨(u, v), hadj⟩
    refine ⟨dart, ?_⟩
    apply Prod.ext
    · apply Prod.ext <;>
        simp [ons_rectDualDartSlot, ons_rectDualVertexSlot, dart, u]
    · have hlt : x.val - 1 < x.val := by omega
      simp [ons_rectDualDartSlot, ons_rectDualDartDirection4, dart, u, v,
        hlt]
  · simp [ons_rectDartValid] at hslot
    have hylt : y.val < N + 1 := ZMod.val_lt y
    have hypos : 0 < y.val := by
      exact Nat.pos_of_ne_zero (fun h ↦ hslot ((ZMod.val_eq_zero y).mp h))
    let u : ons_RectDualVertex M N :=
      (⟨x.val, ZMod.val_lt x⟩, ⟨y.val, ZMod.val_lt y⟩)
    let v : ons_RectDualVertex M N :=
      (⟨x.val, ZMod.val_lt x⟩, ⟨y.val - 1, by omega⟩)
    have hadj : ons_rectDualAdj M N u v := by
      right
      refine ⟨rfl, ?_⟩
      change Nat.dist y.val (y.val - 1) = 1
      rw [Nat.dist_comm,
        Nat.dist_eq_sub_of_le (Nat.sub_le _ _)]
      omega
    let dart : (ons_rectDualGraph M N).Dart := ⟨(u, v), hadj⟩
    refine ⟨dart, ?_⟩
    apply Prod.ext
    · apply Prod.ext <;>
        simp [ons_rectDualDartSlot, ons_rectDualVertexSlot, dart, u]
    · have hlt : y.val - 1 < y.val := by omega
      simp [ons_rectDualDartSlot, ons_rectDualDartDirection4, dart, u, v,
        hlt]


end
end StatMech.Onsager
