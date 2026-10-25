/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Fin.Rev
import Mathlib.Order.Fin.Basic
import Def.Combinatorics.Enumerative.MinimalPermutationsEnumeration.Part3


section

namespace MetaMathlibExt

theorem block1Pos_inj (d : ℕ) (a : Fin (d + 1)) :
    Function.Injective (block1Pos d a) := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [block1Pos_val] at hv
  exact Fin.ext hv

theorem block2Pos_inj (d : ℕ) (a : Fin (d + 1)) :
    Function.Injective (block2Pos d a) := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [block2Pos_val] at hv
  have heq : i.val = j.val := by omega
  exact Fin.ext heq

theorem firstVals_card (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1)) : (firstVals d σ a).card = a.val + 1 := by
  simp only [firstVals, Finset.card_image_of_injective _ (by
    intro i j h
    exact block1Pos_inj d a (σ.injective h)), Finset.card_univ,
    Fintype.card_fin]

theorem secondVals_card (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1)) : (secondVals d σ a).card = (d - a.val) + 1 := by
  simp only [secondVals, Finset.card_image_of_injective _ (by
    intro i j h
    exact block2Pos_inj d a (σ.injective h)), Finset.card_univ,
    Fintype.card_fin]

theorem firstVals_nonempty (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1)) : (firstVals d σ a).Nonempty := by
  have hcard := firstVals_card d σ a
  have hpos : 0 < (firstVals d σ a).card := by omega
  exact Finset.card_pos.mp hpos

theorem secondVals_nonempty (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1)) : (secondVals d σ a).Nonempty := by
  have hcard := secondVals_card d σ a
  have hpos : 0 < (secondVals d σ a).card := by omega
  exact Finset.card_pos.mp hpos

theorem firstVals_min (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a}) :
    (firstVals d σ a).min' (firstVals_nonempty d σ a) = σ a.castSucc := by
  have hanti := block1_anti d σ a ha
  have hlast : (block1Pos d a (Fin.last a.val)).val =
      (a.castSucc : Fin (d + 2)).val := by
    simp only [block1Pos_val, Fin.val_castSucc, Fin.val_last]
  have hbeq : block1Pos d a (Fin.last a.val) = a.castSucc := Fin.ext hlast
  have hle : ∀ y ∈ firstVals d σ a, σ (block1Pos d a (Fin.last a.val)) ≤ y := by
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    rcases lt_or_eq_of_le (Fin.le_last i) with hlt | heq
    · exact le_of_lt (hanti hlt)
    · subst heq
      exact le_refl _
  have hmem : σ (block1Pos d a (Fin.last a.val)) ∈ firstVals d σ a := by
    simp only [firstVals, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨_, rfl⟩
  have hmin_le : (firstVals d σ a).min' (firstVals_nonempty d σ a) ≤
      σ (block1Pos d a (Fin.last a.val)) :=
    Finset.min'_le _ _ hmem
  have hle_min : σ (block1Pos d a (Fin.last a.val)) ≤
      (firstVals d σ a).min' (firstVals_nonempty d σ a) := by
    have hm := Finset.min'_mem (firstVals d σ a) (firstVals_nonempty d σ a)
    exact hle _ hm
  have heq : (firstVals d σ a).min' (firstVals_nonempty d σ a) =
      σ (block1Pos d a (Fin.last a.val)) :=
    le_antisymm hmin_le hle_min
  rw [heq, hbeq]

theorem secondVals_max (d : ℕ) (σ : Equiv.Perm (Fin (d + 2)))
    (a : Fin (d + 1))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a}) :
    (secondVals d σ a).max' (secondVals_nonempty d σ a) = σ a.succ := by
  have hanti := block2_anti d σ a ha
  have hz : (block2Pos d a 0).val = (a.succ : Fin (d + 2)).val := by
    simp only [block2Pos_val, Fin.val_succ, Fin.val_zero]
  have hbeq : block2Pos d a 0 = a.succ := Fin.ext hz
  have hge : ∀ y ∈ secondVals d σ a, y ≤ σ (block2Pos d a 0) := by
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    rcases eq_or_lt_of_le (Fin.zero_le i) with heq | hlt
    · subst heq
      exact le_refl _
    · exact le_of_lt (hanti hlt)
  have hmem : σ (block2Pos d a 0) ∈ secondVals d σ a := by
    simp only [secondVals, Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨0, rfl⟩
  have hmax_ge : σ (block2Pos d a 0) ≤
      (secondVals d σ a).max' (secondVals_nonempty d σ a) :=
    Finset.le_max' _ _ hmem
  have hge_max : (secondVals d σ a).max' (secondVals_nonempty d σ a) ≤
      σ (block2Pos d a 0) := by
    have hm := Finset.max'_mem (secondVals d σ a) (secondVals_nonempty d σ a)
    exact hge _ hm
  have heq : (secondVals d σ a).max' (secondVals_nonempty d σ a) =
      σ (block2Pos d a 0) :=
    le_antisymm hge_max hmax_ge
  rw [heq, hbeq]

end MetaMathlibExt
end
