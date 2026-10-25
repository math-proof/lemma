/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferPairExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferGF2.Part3
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferPairExpansion
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem symmDiff_subset_of_subsets_pair
    {A B S : Finset I} (hA : A ⊆ S) (hB : B ⊆ S) : A ∆ B ⊆ S := by
  intro i hi
  rcases Finset.mem_symmDiff.mp hi with hi | hi
  · exact hA hi.1
  · exact hB hi.1

theorem canonicalTransferSymmDiff_card_le_m
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b : leftMaskFiber ends m j k l zero p) :
    #(canonicalTransferUnion ends m k zero a.1.1 ∆
        canonicalTransferUnion ends m k zero b.1.1) ≤ #m := by
  apply Finset.card_le_card
  exact symmDiff_subset_of_subsets_pair
    (canonicalTransferUnion_subset_m hloop hjk hkl a)
    (canonicalTransferUnion_subset_m hloop hjk hkl b)

theorem nat_pair_encode_lt_iff
    {N x y u v : Nat} (hy : y ≤ N) (hv : v ≤ N) :
    x * (N + 1) + y < u * (N + 1) + v ↔
      x < u ∨ (x = u ∧ y < v) := by
  constructor
  · intro h
    by_cases hxu : x < u
    · exact Or.inl hxu
    have hux : u ≤ x := le_of_not_gt hxu
    by_cases heq : x = u
    · subst u
      exact Or.inr ⟨rfl, Nat.lt_of_add_lt_add_left h⟩
    have hult : u < x := lt_of_le_of_ne hux (Ne.symm heq)
    have hreverse : u * (N + 1) + v < x * (N + 1) + y := by
      calc
        u * (N + 1) + v ≤ u * (N + 1) + N :=
          Nat.add_le_add_left hv _
        _ < u * (N + 1) + (N + 1) := by omega
        _ = (u + 1) * (N + 1) := by rw [Nat.add_mul]; omega
        _ ≤ x * (N + 1) :=
          Nat.mul_le_mul_right (N + 1) (Nat.succ_le_iff.mpr hult)
        _ ≤ x * (N + 1) + y := Nat.le_add_right _ _
    exact False.elim (lt_asymm h hreverse)
  · rintro (hxu | ⟨rfl, hyv⟩)
    · calc
        x * (N + 1) + y ≤ x * (N + 1) + N :=
          Nat.add_le_add_left hy _
        _ < x * (N + 1) + (N + 1) := by omega
        _ = (x + 1) * (N + 1) := by rw [Nat.add_mul]; omega
        _ ≤ u * (N + 1) :=
          Nat.mul_le_mul_right (N + 1) (Nat.succ_le_iff.mpr hxu)
        _ ≤ u * (N + 1) + v := Nat.le_add_right _ _
    · exact Nat.add_lt_add_left hyv _


theorem canonicalCoveragePairScore_lt_iff
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c d : leftMaskFiber ends m j k l zero p) :
    canonicalCoveragePairScore ends m k zero a.1.1 b.1.1 <
        canonicalCoveragePairScore ends m k zero c.1.1 d.1.1 ↔
      #(rowClass m a.1.1 0 ∆ rowClass m b.1.1 0) <
          #(rowClass m c.1.1 0 ∆ rowClass m d.1.1 0) ∨
        (#(rowClass m a.1.1 0 ∆ rowClass m b.1.1 0) =
            #(rowClass m c.1.1 0 ∆ rowClass m d.1.1 0) ∧
          #(canonicalTransferUnion ends m k zero a.1.1 ∆
              canonicalTransferUnion ends m k zero b.1.1) <
            #(canonicalTransferUnion ends m k zero c.1.1 ∆
              canonicalTransferUnion ends m k zero d.1.1)) := by
  have hab := canonicalTransferSymmDiff_card_le_m hloop hjk hkl a b
  have hcd := canonicalTransferSymmDiff_card_le_m hloop hjk hkl c d
  unfold canonicalCoveragePairScore
  exact nat_pair_encode_lt_iff hab hcd


end StatMech.GrahamGHS.FourColor
