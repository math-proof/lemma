/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationTransitionWalk.Part4
import Theorem.StatisticalMechanics.Code.Onsager.DecorationCycleWeight
import Def.StatisticalMechanics.Code.Onsager.DecorationLoopWalk.Part5


namespace StatMech.Onsager

open Finset SimpleGraph

theorem ons_decGeometricLoopStates_valid
    {L n : ℕ} [NeZero n] (d : Fin n → ons_Dart L)
    (hvalid : ∀ k : Fin n,
      (d k).1 = ons_dirStep L (d (k + 1)).2 (d (k + 1)).1) :
    ∀ k : Fin n,
      ons_decGeometricStep L
        (ons_decGeometricLoopStates d k)
        (ons_decGeometricLoopStates d (k + 1)) := by
  intro k
  unfold ons_decGeometricStep ons_decGeometricLoopStates
  have h := hvalid (-(k + 1))
  have hidx : -(k + 1) + 1 = -k := by
    simp
  simpa [hidx] using h

theorem ons_decGeometricLoopStates_sum_exponent
    {L n : ℕ} [NeZero n] (d : Fin n → ons_Dart L) :
    (∑ k : Fin n, ons_decTransitionExponent L
      (ons_decGeometricLoopStates d (k + 1))
      (ons_decGeometricLoopStates d k)) =
        ons_decLoopExponent L d := by
  unfold ons_decGeometricLoopStates ons_decLoopExponent
  let e : Fin n ≃ Fin n :=
    (Equiv.addRight (1 : Fin n)).trans (Equiv.neg (Fin n))
  have hsum := Equiv.sum_comp e
    (fun k : Fin n ↦ ons_decTransitionExponent L (d k) (d (k + 1)))
  simpa [e] using hsum

theorem ons_list_reverse_ofFn
    {alpha : Type*} {n : ℕ} (f : Fin n → alpha) :
    (List.ofFn f).reverse = List.ofFn (fun i ↦ f i.rev) := by
  apply List.ext_getElem
  · simp
  · intro i hi h'i
    rw [List.getElem_reverse, List.getElem_ofFn, List.getElem_ofFn]
    congr 1
    apply Fin.ext
    simp [Fin.val_rev]
    omega

theorem ons_decGeometricLoopStates_tail_reverse
    {L n : ℕ} [NeZero n] (d : Fin n → ons_Dart L) :
    d 0 :: (List.ofFn (ons_decGeometricLoopStates d)).tail.reverse =
      List.ofFn d := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rw [show List.ofFn (ons_decGeometricLoopStates d) =
      d 0 :: List.ofFn
        (fun i : Fin m ↦ ons_decGeometricLoopStates d i.succ) by
    rw [List.ofFn_succ]
    simp [ons_decGeometricLoopStates]]
  simp only [List.tail_cons]
  rw [ons_list_reverse_ofFn, List.ofFn_succ]
  congr 1
  apply congrArg (fun f : Fin m → ons_Dart L ↦ List.ofFn f)
  funext i
  unfold ons_decGeometricLoopStates
  congr 1
  apply Fin.ext
  rw [Fin.val_neg]
  have hne : i.rev.succ ≠ (0 : Fin (m + 1)) := by
    intro hzero
    have hval := congrArg Fin.val hzero
    simp [Fin.val_succ, Fin.val_rev] at hval
  rw [if_neg hne]
  simp only [Fin.val_succ, Fin.val_rev]
  omega

end StatMech.Onsager
