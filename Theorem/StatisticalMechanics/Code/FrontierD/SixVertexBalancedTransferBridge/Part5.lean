/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBalancedTransferBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedBoundaryGluing
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFiniteTorus.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexParticleHole.Part5
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part5
open Finset Matrix


namespace StatMech.FrontierD

theorem svForwardHorizontal_relation {N : Nat} (hN : 0 < N)
    (x y : SixVertexRow N) (hcount : sixVertexUpCount x = sixVertexUpCount y)
    (hpref : svRowPrefixForward x y) :
    svHorizontalPrefixRelation hN x y (svForwardHorizontal x y) := by
  have hlast : svForwardHorizontal x y (svFinLast hN) = false := by
    unfold svForwardHorizontal
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
    have hlastEq : svFinLast hN = Fin.last m := by
      ext
      simp [svFinLast]
    rw [hlastEq]
    have hx := svRowPrefixCount_last x
    have hy := svRowPrefixCount_last y
    rw [hx, hy, hcount]
    simp
  intro k
  have hk := hpref k
  rw [hlast]
  simp only [Bool.toNat_false, zero_add]
  unfold svForwardHorizontal
  by_cases hlt : svRowPrefixCount y k < svRowPrefixCount x k
  · simp [hlt]
    omega
  · simp [hlt]
    omega

theorem svBackwardHorizontal_relation {N : Nat} (hN : 0 < N)
    (x y : SixVertexRow N) (hcount : sixVertexUpCount x = sixVertexUpCount y)
    (hpref : svRowPrefixForward y x) :
    svHorizontalPrefixRelation hN x y (svBackwardHorizontal x y) := by
  have hlast : svBackwardHorizontal x y (svFinLast hN) = true := by
    unfold svBackwardHorizontal
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
    have hlastEq : svFinLast hN = Fin.last m := by
      ext
      simp [svFinLast]
    rw [hlastEq]
    have hx := svRowPrefixCount_last x
    have hy := svRowPrefixCount_last y
    rw [hx, hy, hcount]
    simp
  intro k
  have hk := hpref k
  rw [hlast]
  simp only [Bool.toNat_true]
  unfold svBackwardHorizontal
  by_cases hle : svRowPrefixCount y k ≤ svRowPrefixCount x k
  · simp [hle]
    omega
  · simp [hle]
    omega

theorem svForwardHorizontal_ice {N : Nat} (hN : 0 < N)
    (x y : SixVertexRow N) (hcount : sixVertexUpCount x = sixVertexUpCount y)
    (hpref : svRowPrefixForward x y) :
    svHorizontalIce hN x y (svForwardHorizontal x y) :=
  (svHorizontalIce_iff_prefixRelation hN x y _).2
    (svForwardHorizontal_relation hN x y hcount hpref)

theorem svBackwardHorizontal_ice {N : Nat} (hN : 0 < N)
    (x y : SixVertexRow N) (hcount : sixVertexUpCount x = sixVertexUpCount y)
    (hpref : svRowPrefixForward y x) :
    svHorizontalIce hN x y (svBackwardHorizontal x y) :=
  (svHorizontalIce_iff_prefixRelation hN x y _).2
    (svBackwardHorizontal_relation hN x y hcount hpref)

theorem svRowPrefixCount_finLast {N : Nat} (hN : 0 < N)
    (x : SixVertexRow N) :
    svRowPrefixCount x (svFinLast hN) = sixVertexUpCount x := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  have hlastEq : svFinLast hN = Fin.last m := by
    ext
    simp [svFinLast]
  rw [hlastEq]
  exact svRowPrefixCount_last x

theorem svHorizontalIce_upCount_eq {N : Nat} (hN : 0 < N)
    {x y h : SixVertexRow N} (hice : svHorizontalIce hN x y h) :
    sixVertexUpCount x = sixVertexUpCount y := by
  have hrel := (svHorizontalIce_iff_prefixRelation hN x y h).1 hice
  have hlast := hrel (svFinLast hN)
  rw [svRowPrefixCount_finLast hN x, svRowPrefixCount_finLast hN y] at hlast
  omega

theorem svHorizontalIce_cases {N : Nat} (hN : 0 < N)
    {x y h : SixVertexRow N} (hice : svHorizontalIce hN x y h) :
    (h (svFinLast hN) = false ∧ svRowPrefixForward x y ∧
        h = svForwardHorizontal x y) ∨
      (h (svFinLast hN) = true ∧ svRowPrefixForward y x ∧
        h = svBackwardHorizontal x y) := by
  have hrel := (svHorizontalIce_iff_prefixRelation hN x y h).1 hice
  have hcount := svHorizontalIce_upCount_eq hN hice
  cases hlast : h (svFinLast hN) with
  | false =>
      left
      have hpref : svRowPrefixForward x y := by
        intro k
        have hk := hrel k
        rw [hlast] at hk
        simp only [Bool.toNat_false, zero_add] at hk
        have hb : (h k).toNat ≤ 1 := by cases h k <;> simp
        constructor <;> omega
      refine ⟨rfl, hpref, ?_⟩
      funext k
      have hk := hrel k
      rw [hlast] at hk
      simp only [Bool.toNat_false, zero_add] at hk
      unfold svForwardHorizontal
      by_cases hlt : svRowPrefixCount y k < svRowPrefixCount x k
      · have hone : h k = true := by
          cases hh : h k <;> simp [hh] at hk ⊢ ; omega
        simp [hlt, hone]
      · have hzero : h k = false := by
          cases hh : h k <;> simp [hh] at hk ⊢ ; omega
        simp [hlt, hzero]
  | true =>
      right
      have hpref : svRowPrefixForward y x := by
        intro k
        have hk := hrel k
        rw [hlast] at hk
        simp only [Bool.toNat_true] at hk
        have hb : (h k).toNat ≤ 1 := by cases h k <;> simp
        constructor <;> omega
      refine ⟨rfl, hpref, ?_⟩
      funext k
      have hk := hrel k
      rw [hlast] at hk
      simp only [Bool.toNat_true] at hk
      unfold svBackwardHorizontal
      by_cases hle : svRowPrefixCount y k ≤ svRowPrefixCount x k
      · have hone : h k = true := by
          cases hh : h k <;> simp [hh] at hk ⊢ ; omega
        simp [hle, hone]
      · have hzero : h k = false := by
          cases hh : h k <;> simp [hh] at hk ⊢ ; omega
        simp [hle, hzero]

theorem svRow_eq_of_prefixCount_eq {N : Nat} {x y : SixVertexRow N}
    (hprefix : ∀ k, svRowPrefixCount x k = svRowPrefixCount y k) : x = y := by
  funext k
  cases N with
  | zero => exact Fin.elim0 k
  | succ m =>
      induction k using Fin.induction with
      | zero =>
          have h0 := hprefix (0 : Fin (m + 1))
          rw [svRowPrefixCount_zero, svRowPrefixCount_zero] at h0
          cases hx : x 0 <;> cases hy : y 0 <;> simp [hx, hy] at h0 ⊢
      | succ i ih =>
          have hs := hprefix i.succ
          have hp := hprefix i.castSucc
          rw [svRowPrefixCount_succ, svRowPrefixCount_succ, hp] at hs
          cases hx : x i.succ <;> cases hy : y i.succ <;> simp [hx, hy] at hs ⊢

theorem svRowPrefixForward_antisymm {N : Nat} {x y : SixVertexRow N}
    (hxy : svRowPrefixForward x y) (hyx : svRowPrefixForward y x) : x = y := by
  apply svRow_eq_of_prefixCount_eq
  intro k
  exact Nat.le_antisymm (hyx k).1 (hxy k).1

theorem svForwardHorizontal_last {N : Nat} (hN : 0 < N)
    (x y : SixVertexRow N) (hcount : sixVertexUpCount x = sixVertexUpCount y) :
    svForwardHorizontal x y (svFinLast hN) = false := by
  unfold svForwardHorizontal
  rw [svRowPrefixCount_finLast hN x, svRowPrefixCount_finLast hN y, hcount]
  simp

theorem svBackwardHorizontal_last {N : Nat} (hN : 0 < N)
    (x y : SixVertexRow N) (hcount : sixVertexUpCount x = sixVertexUpCount y) :
    svBackwardHorizontal x y (svFinLast hN) = true := by
  unfold svBackwardHorizontal
  rw [svRowPrefixCount_finLast hN x, svRowPrefixCount_finLast hN y, hcount]
  simp

end StatMech.FrontierD
