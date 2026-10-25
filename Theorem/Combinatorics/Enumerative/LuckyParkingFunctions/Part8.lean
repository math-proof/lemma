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
import Def.Combinatorics.Enumerative.LuckyParkingFunctions.Part7


section

namespace MetaMathlibExt

lemma markedFun_val_of_zero (n : ℕ) (a : Fin n → Fin n)
    (i0 : Fin n) (k : Fin (n + 1)) (h : k.val = 0) :
    (markedFun n a i0 k).val = 0 := by
  simp only [markedFun, dite_eq_left h]

lemma markedFun_val_of_lt (n : ℕ) (a : Fin n → Fin n)
    (i0 : Fin n) (k : Fin (n + 1)) (h0 : ¬ k.val = 0)
    (h1 : k.val - 1 < i0.val) :
    (markedFun n a i0 k).val = (a ⟨k.val - 1, by omega⟩).val := by
  simp only [markedFun, dite_eq_right h0, dite_eq_left h1]

lemma markedFun_val_of_ge (n : ℕ) (a : Fin n → Fin n)
    (i0 : Fin n) (k : Fin (n + 1)) (h0 : ¬ k.val = 0)
    (h1 : ¬ k.val - 1 < i0.val) :
    (markedFun n a i0 k).val =
      (a ⟨k.val - 1, by omega⟩).val + 1 := by
  simp only [markedFun, dite_eq_right h0, dite_eq_right h1]

lemma markedFun_mono (n : ℕ) (a : Fin n → Fin n)
    (ha : Monotone a ∧ ∀ i, (a i).val ≤ i.val) (i0 : Fin n) :
    Monotone (markedFun n a i0) := by
  intro k1 k2 hle
  have hle' : k1.val ≤ k2.val := Fin.le_def.mp hle
  by_cases h10 : k1.val = 0
  · rw [Fin.le_def, markedFun_val_of_zero n a i0 k1 h10]
    exact Nat.zero_le _
  · by_cases h20 : k2.val = 0
    · have hcon : k1.val = 0 := by
        omega
      exact absurd hcon h10
    · by_cases h11 : k1.val - 1 < i0.val
      · by_cases h21 : k2.val - 1 < i0.val
        · rw [Fin.le_def]
          rw [markedFun_val_of_lt n a i0 k1 h10 h11]
          rw [markedFun_val_of_lt n a i0 k2 h20 h21]
          have hmon :
              a ⟨k1.val - 1, by omega⟩ ≤ a ⟨k2.val - 1, by omega⟩ := by
            apply ha.1
            rw [Fin.le_def]
            simp only
            omega
          exact Fin.le_def.mp hmon
        · rw [Fin.le_def]
          rw [markedFun_val_of_lt n a i0 k1 h10 h11]
          rw [markedFun_val_of_ge n a i0 k2 h20 h21]
          have hmon :
              a ⟨k1.val - 1, by omega⟩ ≤ a ⟨k2.val - 1, by omega⟩ := by
            apply ha.1
            rw [Fin.le_def]
            simp only
            omega
          have h := Fin.le_def.mp hmon
          omega
      · by_cases h21 : k2.val - 1 < i0.val
        · have hcon : k1.val - 1 < i0.val := by
            omega
          exact absurd hcon h11
        · rw [Fin.le_def]
          rw [markedFun_val_of_ge n a i0 k1 h10 h11]
          rw [markedFun_val_of_ge n a i0 k2 h20 h21]
          have hmon :
              a ⟨k1.val - 1, by omega⟩ ≤ a ⟨k2.val - 1, by omega⟩ := by
            apply ha.1
            rw [Fin.le_def]
            simp only
            omega
          have h := Fin.le_def.mp hmon
          omega

lemma markedFun_bound (n : ℕ) (a : Fin n → Fin n)
    (ha : Monotone a ∧ ∀ i, (a i).val ≤ i.val) (i0 : Fin n)
    (k : Fin (n + 1)) : (markedFun n a i0 k).val ≤ k.val := by
  by_cases h0 : k.val = 0
  · rw [markedFun_val_of_zero n a i0 k h0]
    omega
  · by_cases h1 : k.val - 1 < i0.val
    · rw [markedFun_val_of_lt n a i0 k h0 h1]
      have hb := ha.2 ⟨k.val - 1, by omega⟩
      simp only at hb
      omega
    · rw [markedFun_val_of_ge n a i0 k h0 h1]
      have hb := ha.2 ⟨k.val - 1, by omega⟩
      simp only at hb
      omega

end MetaMathlibExt
end
