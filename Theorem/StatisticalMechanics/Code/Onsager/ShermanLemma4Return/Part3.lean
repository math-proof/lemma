/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanLemma4Return.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLoop
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLemma4.Part3
import Def.StatisticalMechanics.Code.Onsager.ShermanLemma4Return.Part2


namespace StatMech.Onsager

open Matrix BigOperators Finset Complex

set_option linter.unusedSectionVars false

section FirstReturn

variable {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ} [NeZero n]


theorem ons_mem_rootedAvoiding (e : E) (rev : E → E) (v : Fin n → E) :
    v ∈ ons_rootedAvoiding (n := n) e rev ↔ v 0 = e ∧ (∀ k : Fin n, v k ≠ rev e) := by
  unfold ons_rootedAvoiding; simp


theorem ons_firstReturn_mem_rootedAvoiding {e : E} {rev : E → E} {v : Fin n → E}
    (h : ons_isFirstReturn e rev v) : v ∈ ons_rootedAvoiding (n := n) e rev := by
  rw [ons_mem_rootedAvoiding]
  exact ⟨h.1, h.2.2⟩

end FirstReturn

section Concat

variable {E : Type*} {n m : ℕ} [NeZero n] [NeZero m]


theorem ons_val_one_add : ((1 : Fin (n + m)).val) = 1 := by
  have hn := NeZero.pos n
  have hm := NeZero.pos m
  haveI : NeZero (n + m) := ⟨by omega⟩
  rw [Fin.val_one']
  exact Nat.mod_eq_of_lt (by omega)


theorem ons_append_succ_left (u : Fin n → E) (w : Fin m → E) (hw : w 0 = u 0) (i : Fin n) :
    Fin.append u w ((Fin.castAdd m i) + 1) = u (i + 1) := by
  have hn := NeZero.pos n
  have hm := NeZero.pos m
  haveI : NeZero (n + m) := ⟨by omega⟩
  have hi : i.val < n := i.isLt
  have hsval : ((Fin.castAdd m i) + 1 : Fin (n + m)).val = i.val + 1 := by
    rw [Fin.val_add, Fin.val_castAdd, ons_val_one_add]
    exact Nat.mod_eq_of_lt (by omega)
  by_cases hlt : i.val + 1 < n
  · 
    have he : ((Fin.castAdd m i) + 1 : Fin (n + m)) = Fin.castAdd m ⟨i.val + 1, hlt⟩ := by
      apply Fin.ext; rw [hsval, Fin.val_castAdd]
    have hi1 : (i + 1 : Fin n) = ⟨i.val + 1, hlt⟩ := by
      apply Fin.ext
      rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < n by omega)]
      exact Nat.mod_eq_of_lt (by omega)
    rw [he, Fin.append_left, hi1]
  · 
    have hin : i.val + 1 = n := by omega
    have he : ((Fin.castAdd m i) + 1 : Fin (n + m)) = Fin.natAdd n (0 : Fin m) := by
      apply Fin.ext; rw [hsval, Fin.val_natAdd, Fin.val_zero]; omega
    have hi1 : (i + 1 : Fin n) = 0 := by
      apply Fin.ext
      rw [Fin.val_zero, Fin.val_add, Fin.val_one']
      rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)) with h1 | h1
      · subst h1; simp
      · rw [Nat.mod_eq_of_lt h1, hin, Nat.mod_self]
    rw [he, Fin.append_right, hi1, hw]


theorem ons_append_succ_right (u : Fin n → E) (w : Fin m → E) (hw : w 0 = u 0) (i : Fin m) :
    Fin.append u w ((Fin.natAdd n i) + 1) = w (i + 1) := by
  have hn := NeZero.pos n
  have hm := NeZero.pos m
  haveI : NeZero (n + m) := ⟨by omega⟩
  have hi : i.val < m := i.isLt
  by_cases hlt : i.val + 1 < m
  · 
    have hsval : ((Fin.natAdd n i) + 1 : Fin (n + m)).val = n + i.val + 1 := by
      rw [Fin.val_add, Fin.val_natAdd, ons_val_one_add]
      exact Nat.mod_eq_of_lt (by omega)
    have he : ((Fin.natAdd n i) + 1 : Fin (n + m)) = Fin.natAdd n ⟨i.val + 1, hlt⟩ := by
      apply Fin.ext; rw [hsval, Fin.val_natAdd]; rfl
    have hi1 : (i + 1 : Fin m) = ⟨i.val + 1, hlt⟩ := by
      apply Fin.ext
      rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < m by omega)]
      exact Nat.mod_eq_of_lt (by omega)
    rw [he, Fin.append_right, hi1]
  · 
    have him : i.val + 1 = m := by omega
    have hsval : ((Fin.natAdd n i) + 1 : Fin (n + m)).val = 0 := by
      rw [Fin.val_add, Fin.val_natAdd, ons_val_one_add]
      have : n + i.val + 1 = n + m := by omega
      rw [this, Nat.mod_self]
    have he : ((Fin.natAdd n i) + 1 : Fin (n + m)) = Fin.castAdd m (0 : Fin n) := by
      apply Fin.ext; rw [hsval, Fin.val_castAdd, Fin.val_zero]
    have hi1 : (i + 1 : Fin m) = 0 := by
      apply Fin.ext
      rw [Fin.val_zero, Fin.val_add, Fin.val_one']
      rcases eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)) with h1 | h1
      · subst h1; simp
      · rw [Nat.mod_eq_of_lt h1, him, Nat.mod_self]
    rw [he, Fin.append_left, hi1, hw]


theorem ons_loopWeight_concat [Fintype E] [DecidableEq E] (Λ : Matrix E E ℂ)
    (u : Fin n → E) (w : Fin m → E) (hw : w 0 = u 0) :
    haveI : NeZero (n + m) := ⟨by have := NeZero.pos n; omega⟩
    ons_loopWeight Λ (Fin.append u w) = ons_loopWeight Λ u * ons_loopWeight Λ w := by
  haveI : NeZero (n + m) := ⟨by have := NeZero.pos n; omega⟩
  unfold ons_loopWeight
  rw [Fin.prod_univ_add (f := fun k => Λ (Fin.append u w k) (Fin.append u w (k + 1)))]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    rw [Fin.append_left, ons_append_succ_left u w hw i]
  · apply Finset.prod_congr rfl
    intro i _
    rw [Fin.append_right, ons_append_succ_right u w hw i]

end Concat

section Assembly


theorem ons_lemma4_of_factorization {z : ℂ} (hz : ‖z‖ < 1) (perK : ℕ → ℂ)
    (hcount : ∀ k : ℕ, perK k = z ^ (k + 1)) :
    (∑' k : ℕ, perK k / (k + 1)) = -Complex.log (1 - z) ∧
      Complex.exp (-(∑' k : ℕ, perK k / (k + 1))) = 1 - z := by
  have hsum : (∑' k : ℕ, perK k / (k + 1)) = ∑' k : ℕ, z ^ (k + 1) / (k + 1) := by
    apply tsum_congr
    intro k
    rw [hcount k]
  refine ⟨?_, ?_⟩
  · rw [hsum]; exact ons_lemma4_geometric hz
  · rw [hsum]; exact ons_lemma4_exp hz

end Assembly
end StatMech.Onsager
