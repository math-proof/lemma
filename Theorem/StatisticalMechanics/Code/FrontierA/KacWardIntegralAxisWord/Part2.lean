/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisWord.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRationalNormalization.Part3
import Def.StatisticalMechanics.Code.FrontierA.KacWardIntegralAxisWord.Part2


namespace StatMech.FrontierA

open StatMech.Onsager.BaseCase


theorem kwIntegralPolygonEdgeWord_step_sum
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ) (i : Fin n) :
    ((kwIntegralPolygonEdgeWord p i).map stepOf).sum =
      p (i + 1) - p i :=
  kwIntegralAxisWord_step_sum _


theorem kwIntegralPolygonWord_step_sum
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ) :
    ((kwIntegralPolygonWord p).map stepOf).sum = 0 := by
  calc
    ((kwIntegralPolygonWord p).map stepOf).sum =
        (List.ofFn (fun i : Fin n ↦
          ((kwIntegralPolygonEdgeWord p i).map stepOf).sum)).sum := by
      simp [kwIntegralPolygonWord]
      rfl
    _ =
        ∑ i : Fin n, ((kwIntegralPolygonEdgeWord p i).map stepOf).sum := by
      rw [List.sum_ofFn]
    _ = ∑ i : Fin n, (p (i + 1) - p i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact kwIntegralPolygonEdgeWord_step_sum p i
    _ = 0 := by
      rw [Finset.sum_sub_distrib]
      have hshift : (∑ i : Fin n, p (i + 1)) = ∑ i : Fin n, p i :=
        Equiv.sum_comp (Equiv.addRight (1 : Fin n)) p
      rw [hshift, sub_self]


theorem kwIntegralPolygonWord_ne_nil
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ)
    (hn : 2 ≤ n) (hp : Function.Injective p) :
    kwIntegralPolygonWord p ≠ [] := by
  have hedge : p ((0 : Fin n) + 1) - p 0 ≠ 0 := by
    rw [sub_ne_zero]
    exact hp.ne (by
      apply Fin.ne_of_val_ne
      simp [Nat.mod_eq_of_lt hn])
  have hword := kwIntegralAxisWord_ne_nil hedge
  obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ hword
  intro hempty
  have hdall : d ∈ kwIntegralPolygonWord p := by
    rw [kwIntegralPolygonWord, List.mem_flatten]
    refine ⟨kwIntegralPolygonEdgeWord p 0, ?_, hd⟩
    exact List.mem_ofFn.mpr ⟨0, rfl⟩
  simp only [hempty, List.not_mem_nil] at hdall


end StatMech.FrontierA
