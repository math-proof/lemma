/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part13
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDefectDynamics.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexSectorPosition_forwardMoveSector
    {N n : Nat} (x : SixVertexSector N n) (a : Fin n → Nat)
    (hbound : ∀ i, (sixVertexSectorPosition x i).val + a i < N)
    (hmono : ∀ i j : Fin n, i < j →
      (sixVertexSectorPosition x i).val + a i <
        (sixVertexSectorPosition x j).val + a j) :
    sixVertexSectorPosition
      (sixVertexForwardMoveSector x a hbound hmono) =
        sixVertexForwardMoveEmbedding x a hbound hmono := by
  change Set.powersetCard.ofFinEmbEquiv.symm
      (Set.powersetCard.ofFinEmbEquiv
        (sixVertexForwardMoveEmbedding x a hbound hmono)) = _
  exact Equiv.symm_apply_apply _ _

@[simp] theorem sixVertexSectorPosition_forwardMoveSector_apply_val
    {N n : Nat} (x : SixVertexSector N n) (a : Fin n → Nat)
    (hbound : ∀ i, (sixVertexSectorPosition x i).val + a i < N)
    (hmono : ∀ i j : Fin n, i < j →
      (sixVertexSectorPosition x i).val + a i <
        (sixVertexSectorPosition x j).val + a j)
    (i : Fin n) :
    (sixVertexSectorPosition
      (sixVertexForwardMoveSector x a hbound hmono) i).val =
        (sixVertexSectorPosition x i).val + a i := by
  rw [sixVertexSectorPosition_forwardMoveSector]
  rfl

theorem sixVertexInfinityGraph_adj_forwardMoveSector
    {N n : Nat} (hn : 0 < n) (x : SixVertexSector N n)
    (a : Fin n → Nat)
    (hbound : ∀ i, (sixVertexSectorPosition x i).val + a i < N)
    (hmono : ∀ i j : Fin n, i < j →
      (sixVertexSectorPosition x i).val + a i <
        (sixVertexSectorPosition x j).val + a j)
    (hpos : ∀ i, 0 < a i)
    (hbetween : ∀ (k : Nat) (hk : k + 1 < n),
      (sixVertexSectorPosition x ⟨k, by omega⟩).val +
          a ⟨k, by omega⟩ <
        (sixVertexSectorPosition x ⟨k + 1, hk⟩).val) :
    (sixVertexInfinityGraph N n).Adj x
      (sixVertexForwardMoveSector x a hbound hmono) := by
  let y := sixVertexForwardMoveSector x a hbound hmono
  have hypos (i : Fin n) :
      (sixVertexSectorPosition y i).val =
        (sixVertexSectorPosition x i).val + a i := by
    exact sixVertexSectorPosition_forwardMoveSector_apply_val
      x a hbound hmono i
  have hforward : SixVertexForwardInterlaced
      (sixVertexSectorRow x) (sixVertexSectorRow y) := by
    apply sixVertexForwardInterlaced_of_positions
    constructor
    · intro i
      exact_mod_cast (show (sixVertexSectorPosition x i).val ≤
        (sixVertexSectorPosition y i).val by rw [hypos]; omega)
    · intro k hk
      exact_mod_cast (show (sixVertexSectorPosition y ⟨k, by omega⟩).val ≤
        (sixVertexSectorPosition x ⟨k + 1, hk⟩).val by
          rw [hypos]
          exact (hbetween k hk).le)
  have hdisj : Disjoint (x : Finset (Fin N)) (y : Finset (Fin N)) := by
    rw [Finset.disjoint_left]
    intro z hzx hzy
    let j : Fin n := (x.val.orderIsoOfFin x.prop).symm ⟨z, hzx⟩
    let i : Fin n := (y.val.orderIsoOfFin y.prop).symm ⟨z, hzy⟩
    have hj : sixVertexSectorPosition x j = z := by
      exact congrArg Subtype.val
        ((x.val.orderIsoOfFin x.prop).apply_symm_apply ⟨z, hzx⟩)
    have hi : sixVertexSectorPosition y i = z := by
      exact congrArg Subtype.val
        ((y.val.orderIsoOfFin y.prop).apply_symm_apply ⟨z, hzy⟩)
    have heq : sixVertexSectorPosition x j =
        sixVertexSectorPosition y i := hj.trans hi.symm
    by_cases hji : j ≤ i
    · have hxle : (sixVertexSectorPosition x j).val ≤
          (sixVertexSectorPosition x i).val := by
        exact_mod_cast (sixVertexSectorPosition x).monotone hji
      have hygt : (sixVertexSectorPosition x i).val <
          (sixVertexSectorPosition y i).val := by
        rw [hypos i]
        exact Nat.lt_add_of_pos_right (hpos i)
      have := congrArg Fin.val heq
      omega
    · have hij : i < j := lt_of_not_ge hji
      have hik : i.val + 1 < n := by omega
      have hmid := hbetween i.val hik
      have hi0 : (⟨i.val, by omega⟩ : Fin n) = i := Fin.ext rfl
      rw [hi0] at hmid
      have hnextle :
          (sixVertexSectorPosition x ⟨i.val + 1, hik⟩).val ≤
            (sixVertexSectorPosition x j).val := by
        exact_mod_cast (sixVertexSectorPosition x).monotone (by
          change i.val + 1 ≤ j.val
          omega)
      have := congrArg Fin.val heq
      rw [hypos] at this
      omega
  exact (sixVertexInfinityGraph_adj_iff_forward_disjoint hn x y).mpr
    (Or.inl ⟨hforward, hdisj⟩)

theorem sixVertexSectorCyclicNext_pred
    {n : Nat} (i : Fin n) (hi : 0 < i.val) :
    sixVertexSectorCyclicNext ⟨i.val - 1, by omega⟩ = i := by
  rw [sixVertexSectorCyclicNext]
  split_ifs with hnext
  · apply Fin.ext
    change (i.val - 1) + 1 = i.val
    omega
  · exfalso
    apply hnext
    change (i.val - 1) + 1 < n
    omega

theorem sixVertexSectorCyclicNext_eq_iff_eq_pred
    {n : Nat} (i j : Fin n) (hi : 0 < i.val) :
    sixVertexSectorCyclicNext j = i ↔
      j = ⟨i.val - 1, by omega⟩ := by
  constructor
  · intro h
    rw [sixVertexSectorCyclicNext] at h
    split_ifs at h with hnext
    · apply Fin.ext
      have hv := congrArg Fin.val h
      change j.val + 1 = i.val at hv
      change j.val = i.val - 1
      omega
    · have hv := congrArg Fin.val h
      change 0 = i.val at hv
      omega
  · rintro rfl
    exact sixVertexSectorCyclicNext_pred i hi


end
end StatMech.FrontierD
