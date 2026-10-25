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
import Def.Combinatorics.Enumerative.MinimalPermutationsEnumeration.Part10


section

namespace MetaMathlibExt

theorem mpeConstruct_block1 (d : ℕ) (a : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1)
    (i : Fin (a.val + 1)) :
    mpeConstruct d a L hL (block1Pos d a i) =
      L.orderEmbOfFin hL (Fin.rev i) := by
  rw [mpeConstruct_apply]
  have hi : (block1Pos d a i).val ≤ a.val := by
    simp only [block1Pos_val]
    omega
  simp only [mpeConstructFun, hi, ↓reduceDIte]
  have hidx : mpeFirstIndex d a (block1Pos d a i) hi = i := by
    apply Fin.ext
    simp only [mpeFirstIndex_val, block1Pos_val]
  rw [hidx]

theorem mpeConstruct_block2 (d : ℕ) (a : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1)
    (i : Fin ((d - a.val) + 1)) :
    mpeConstruct d a L hL (block2Pos d a i) =
      Lᶜ.orderEmbOfFin (mpe_compl_card d a L hL) (Fin.rev i) := by
  rw [mpeConstruct_apply]
  have hi : ¬(block2Pos d a i).val ≤ a.val := by
    simp only [block2Pos_val]
    omega
  simp only [mpeConstructFun, hi, ↓reduceDIte]
  have hidx : mpeSecondIndex d a (block2Pos d a i) hi = i := by
    apply Fin.ext
    simp only [mpeSecondIndex_val, block2Pos_val]
    omega
  rw [hidx]

theorem mpeConstruct_block1_anti (d : ℕ) (a : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1) :
    StrictAnti (fun i : Fin (a.val + 1) =>
      mpeConstruct d a L hL (block1Pos d a i)) := by
  intro i j hij
  change mpeConstruct d a L hL (block1Pos d a j) <
    mpeConstruct d a L hL (block1Pos d a i)
  rw [mpeConstruct_block1, mpeConstruct_block1]
  exact (L.orderEmbOfFin hL).strictMono (Fin.rev_strictAnti hij)

theorem mpeConstruct_block2_anti (d : ℕ) (a : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1) :
    StrictAnti (fun i : Fin ((d - a.val) + 1) =>
      mpeConstruct d a L hL (block2Pos d a i)) := by
  intro i j hij
  change mpeConstruct d a L hL (block2Pos d a j) <
    mpeConstruct d a L hL (block2Pos d a i)
  rw [mpeConstruct_block2, mpeConstruct_block2]
  exact (Lᶜ.orderEmbOfFin (mpe_compl_card d a L hL)).strictMono
    (Fin.rev_strictAnti hij)

theorem mpeConstruct_firstVals (d : ℕ) (a : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1) :
    firstVals d (mpeConstruct d a L hL) a = L := by
  ext y
  simp only [firstVals, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    rw [mpeConstruct_block1]
    exact Finset.orderEmbOfFin_mem L hL _
  · intro hy
    have hy' : y ∈ Finset.image (L.orderEmbOfFin hL) Finset.univ := by
      rw [Finset.image_orderEmbOfFin_univ]
      exact hy
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hy'
    refine ⟨Fin.rev i, ?_⟩
    rw [mpeConstruct_block1, Fin.rev_rev]
    exact hi

theorem mpeConstruct_left_endpoint (d : ℕ) (a : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1) :
    mpeConstruct d a L hL a.castSucc =
      L.orderEmbOfFin hL 0 := by
  have heq : a.castSucc = block1Pos d a (Fin.last a.val) := by
    apply Fin.ext
    simp only [Fin.val_castSucc, block1Pos_val, Fin.val_last]
  rw [heq, mpeConstruct_block1, Fin.rev_last]

theorem mpeConstruct_right_endpoint (d : ℕ) (a : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1) :
    mpeConstruct d a L hL a.succ =
      Lᶜ.orderEmbOfFin (mpe_compl_card d a L hL) (Fin.last (d - a.val)) := by
  have heq : a.succ = block2Pos d a 0 := by
    apply Fin.ext
    simp only [Fin.val_succ, block2Pos_val, Fin.val_zero, add_zero]
  rw [heq, mpeConstruct_block2, Fin.rev_zero]

theorem mpeConstruct_memB_of_gap_descent (d : ℕ) (a : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1)
    (hdesc : mpeConstruct d a L hL a.succ < mpeConstruct d a L hL a.castSucc) :
    L ∈ exclB d a := by
  have hright : ∀ y ∈ Lᶜ, y ≤ mpeConstruct d a L hL a.succ := by
    intro y hy
    have hy' : y ∈ Finset.image
        (Lᶜ.orderEmbOfFin (mpe_compl_card d a L hL)) Finset.univ := by
      rw [Finset.image_orderEmbOfFin_univ]
      exact hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy'
    rw [mpeConstruct_right_endpoint]
    exact (Lᶜ.orderEmbOfFin (mpe_compl_card d a L hL)).monotone (Fin.le_last i)
  have hsubC : Lᶜ ⊆ Finset.Iic (mpeConstruct d a L hL a.succ) := by
    intro y hy
    exact Finset.mem_Iic.mpr (hright y hy)
  have hcard := Finset.card_le_card hsubC
  rw [mpe_compl_card d a L hL] at hcard
  simp only [Fin.card_Iic] at hcard
  have hsubL : L ⊆ topLarge d a := by
    intro x hx
    have hx' : x ∈ Finset.image (L.orderEmbOfFin hL) Finset.univ := by
      rw [Finset.image_orderEmbOfFin_univ]
      exact hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx'
    have hleft : mpeConstruct d a L hL a.castSucc ≤ L.orderEmbOfFin hL i := by
      rw [mpeConstruct_left_endpoint]
      exact (L.orderEmbOfFin hL).monotone (Fin.zero_le i)
    simp only [topLarge, Finset.mem_Ici]
    change d - a.val ≤ (L.orderEmbOfFin hL i).val
    omega
  simp only [exclB, Finset.mem_filter, Finset.mem_powersetCard]
  exact ⟨⟨Finset.subset_univ _, hL⟩, hsubL⟩

theorem mpeConstruct_gap_ascent (d : ℕ) (a : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1)
    (hB : L ∉ exclB d a) :
    mpeConstruct d a L hL a.castSucc < mpeConstruct d a L hL a.succ := by
  have hposne : a.castSucc ≠ a.succ := by
    intro heq
    have hv := congrArg Fin.val heq
    simp only [Fin.val_castSucc, Fin.val_succ] at hv
    omega
  have hne : mpeConstruct d a L hL a.castSucc ≠
      mpeConstruct d a L hL a.succ :=
    fun heq => hposne ((mpeConstruct d a L hL).injective heq)
  rcases lt_or_gt_of_ne hne with hasc | hdesc
  · exact hasc
  · exact absurd (mpeConstruct_memB_of_gap_descent d a L hL hdesc) hB

theorem mpeConstruct_descent_of_ne (d : ℕ) (a k : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1) (hk : k ≠ a) :
    mpeConstruct d a L hL k.succ < mpeConstruct d a L hL k.castSucc := by
  have hvne : k.val ≠ a.val := fun heq => hk (Fin.ext heq)
  rcases lt_or_gt_of_ne hvne with hlt | hgt
  · let i : Fin a.val := ⟨k.val, hlt⟩
    have hi : i.castSucc < i.succ := by
      change i.val < i.val + 1
      omega
    have hdesc := mpeConstruct_block1_anti d a L hL hi
    have heq1 : block1Pos d a i.castSucc = k.castSucc := by
      apply Fin.ext
      simp only [block1Pos_val, Fin.val_castSucc]
      rfl
    have heq2 : block1Pos d a i.succ = k.succ := by
      apply Fin.ext
      simp only [block1Pos_val, Fin.val_succ]
      rfl
    change mpeConstruct d a L hL (block1Pos d a i.succ) <
      mpeConstruct d a L hL (block1Pos d a i.castSucc) at hdesc
    rw [heq1, heq2] at hdesc
    exact hdesc
  · have hklt := k.isLt
    have ha := a.isLt
    let i : Fin (d - a.val) := ⟨k.val - (a.val + 1), by omega⟩
    have hi : i.castSucc < i.succ := by
      change i.val < i.val + 1
      omega
    have hdesc := mpeConstruct_block2_anti d a L hL hi
    have heq1 : block2Pos d a i.castSucc = k.castSucc := by
      apply Fin.ext
      simp only [block2Pos_val, Fin.val_castSucc]
      change a.val + 1 + (k.val - (a.val + 1)) = k.val
      omega
    have heq2 : block2Pos d a i.succ = k.succ := by
      apply Fin.ext
      simp only [block2Pos_val, Fin.val_succ]
      change a.val + 1 + (k.val - (a.val + 1) + 1) = k.val + 1
      omega
    change mpeConstruct d a L hL (block2Pos d a i.succ) <
      mpeConstruct d a L hL (block2Pos d a i.castSucc) at hdesc
    rw [heq1, heq2] at hdesc
    exact hdesc

theorem mpeConstruct_ascent_singleton (d : ℕ) (a : Fin (d + 1))
    (L : Finset (Fin (d + 2))) (hL : L.card = a.val + 1)
    (hB : L ∉ exclB d a) :
    (Finset.univ.filter fun i : Fin (d + 1) =>
      mpeConstruct d a L hL i.castSucc < mpeConstruct d a L hL i.succ) = {a} := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hasc
    by_contra hk
    have hdesc := mpeConstruct_descent_of_ne d a k L hL hk
    exact (lt_asymm hasc hdesc)
  · intro hk
    subst k
    exact mpeConstruct_gap_ascent d a L hL hB

end MetaMathlibExt
end
