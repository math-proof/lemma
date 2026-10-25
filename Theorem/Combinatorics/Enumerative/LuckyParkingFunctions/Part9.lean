/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean -/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.LuckyParkingFunctions.Part8


section

namespace MetaMathlibExt

lemma marked_fixed (n : ℕ) (m : Marked n) :
    (embedMarked n m).1 ⟨m.2.1.val + 1, by omega⟩ =
      ⟨m.2.1.val + 1, by omega⟩ := by
  obtain ⟨⟨a, ha⟩, ⟨i0, hi⟩⟩ := m
  apply Fin.ext
  have h0 : ¬ (⟨i0.val + 1, by omega⟩ : Fin (n + 1)).val = 0 := by
    simp only
    omega
  have h1 :
      ¬ (⟨i0.val + 1, by omega⟩ : Fin (n + 1)).val - 1 < i0.val := by
    simp only
    omega
  have hB := markedFun_val_of_ge n a i0 ⟨i0.val + 1, by omega⟩ h0 h1
  simp only [embedMarked] at hB ⊢
  rw [hB]
  have heq :
      ∀ h' : (⟨i0.val + 1, by omega⟩ : Fin (n + 1)).val - 1 < n,
        (⟨(⟨i0.val + 1, by omega⟩ : Fin (n + 1)).val - 1, h'⟩ : Fin n) =
          i0 := by
    intro _
    apply Fin.ext
    simp only
    omega
  have hAi : a ⟨(⟨i0.val + 1, by omega⟩ : Fin (n + 1)).val - 1, by omega⟩ =
      i0 := by
    rw [heq _]
    exact hi
  have hval := congrArg Fin.val hAi
  simp only at hval ⊢
  omega

lemma embedMarked_injective (n : ℕ) :
    Function.Injective (embedMarked n) := by
  intro m1 m2 heq
  have hi_eq : m1.2.1.val = m2.2.1.val := by
    have h12 : ¬ m1.2.1.val < m2.2.1.val := by
      intro hlt
      have hpos :
          0 < (⟨m1.2.1.val + 1, by omega⟩ : Fin (n + 1)).val := by
        simp only
        omega
      have hlt2 :
          (⟨m1.2.1.val + 1, by omega⟩ : Fin (n + 1)).val <
            m2.2.1.val + 1 := by
        simp only
        omega
      have hNe := marked_no_small_fixed n m2 ⟨m1.2.1.val + 1, by omega⟩
        hpos hlt2
      have hFix1 := marked_fixed n m1
      have heq' :
          (embedMarked n m1).1 ⟨m1.2.1.val + 1, by omega⟩ =
            (embedMarked n m2).1 ⟨m1.2.1.val + 1, by omega⟩ := by
        rw [heq]
      have hFix2 :
          (embedMarked n m2).1 ⟨m1.2.1.val + 1, by omega⟩ =
            ⟨m1.2.1.val + 1, by omega⟩ := by
        rw [← heq']
        exact hFix1
      exact hNe hFix2
    have h21 : ¬ m2.2.1.val < m1.2.1.val := by
      intro hlt
      have hpos :
          0 < (⟨m2.2.1.val + 1, by omega⟩ : Fin (n + 1)).val := by
        simp only
        omega
      have hlt2 :
          (⟨m2.2.1.val + 1, by omega⟩ : Fin (n + 1)).val <
            m1.2.1.val + 1 := by
        simp only
        omega
      have hNe := marked_no_small_fixed n m1 ⟨m2.2.1.val + 1, by omega⟩
        hpos hlt2
      have hFix2 := marked_fixed n m2
      have heq' :
          (embedMarked n m1).1 ⟨m2.2.1.val + 1, by omega⟩ =
            (embedMarked n m2).1 ⟨m2.2.1.val + 1, by omega⟩ := by
        rw [heq]
      have hFix1 :
          (embedMarked n m1).1 ⟨m2.2.1.val + 1, by omega⟩ =
            ⟨m2.2.1.val + 1, by omega⟩ := by
        rw [heq']
        exact hFix2
      exact hNe hFix1
    omega
  have ha_eq : m1.1.1 = m2.1.1 := by
    funext j
    apply Fin.ext
    have h0 : (⟨j.val + 1, by omega⟩ : Fin (n + 1)).val ≠ 0 := by
      simp only
      omega
    have heq_k :
        ((embedMarked n m1).1 ⟨j.val + 1, by omega⟩).val =
          ((embedMarked n m2).1 ⟨j.val + 1, by omega⟩).val := by
      rw [heq]
    simp only [embedMarked] at heq_k
    by_cases h1 : (⟨j.val + 1, by omega⟩ : Fin (n + 1)).val - 1 <
        m1.2.1.val
    · have h2 : (⟨j.val + 1, by omega⟩ : Fin (n + 1)).val - 1 <
          m2.2.1.val := by
        omega
      have hB1 := markedFun_val_of_lt n m1.1.1 m1.2.1
        ⟨j.val + 1, by omega⟩ h0 h1
      have hB2 := markedFun_val_of_lt n m2.1.1 m2.2.1
        ⟨j.val + 1, by omega⟩ h0 h2
      rw [hB1, hB2] at heq_k
      exact heq_k
    · have h2 : ¬ (⟨j.val + 1, by omega⟩ : Fin (n + 1)).val - 1 <
          m2.2.1.val := by
        omega
      have hB1 := markedFun_val_of_ge n m1.1.1 m1.2.1
        ⟨j.val + 1, by omega⟩ h0 h1
      have hB2 := markedFun_val_of_ge n m2.1.1 m2.2.1
        ⟨j.val + 1, by omega⟩ h0 h2
      rw [hB1, hB2] at heq_k
      have heq_k' : (m1.1.1 j).val + 1 = (m2.1.1 j).val + 1 := heq_k
      omega
  obtain ⟨⟨a1f, ha1⟩, ⟨i1, hi1⟩⟩ := m1
  obtain ⟨⟨a2f, ha2⟩, ⟨i2, hi2⟩⟩ := m2
  have hi_eq' : i1.val = i2.val := hi_eq
  have hi_fin : i1 = i2 := Fin.ext hi_eq'
  have ha_fun : a1f = a2f := ha_eq
  subst ha_fun
  subst hi_fin
  rfl

lemma embed_disjoint (n : ℕ) (a : Park n) (m : Marked n) :
    embedPlain n a ≠ embedMarked n m := by
  intro heq
  have hFix := marked_fixed n m
  have hpos : 0 < (⟨m.2.1.val + 1, by omega⟩ : Fin (n + 1)).val := by
    simp only
    omega
  have hNe := plain_no_fixed n a ⟨m.2.1.val + 1, by omega⟩ hpos
  have heq' : (embedPlain n a).1 ⟨m.2.1.val + 1, by omega⟩ =
      ⟨m.2.1.val + 1, by omega⟩ := by
    rw [heq]
    exact hFix
  exact hNe heq'

end MetaMathlibExt
end
