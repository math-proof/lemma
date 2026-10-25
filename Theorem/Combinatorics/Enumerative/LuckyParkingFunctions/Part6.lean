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
import Def.Combinatorics.Enumerative.LuckyParkingFunctions.Part5


section

namespace MetaMathlibExt

lemma plainFun_val_of_zero (n : ℕ) (a : Fin n → Fin n)
    (k : Fin (n + 1)) (h : k.val = 0) :
    (plainFun n a k).val = 0 := by
  simp only [plainFun, dite_eq_left h]

lemma plainFun_val_of_ne (n : ℕ) (a : Fin n → Fin n)
    (k : Fin (n + 1)) (h : ¬ k.val = 0) :
    (plainFun n a k).val = (a ⟨k.val - 1, by omega⟩).val := by
  simp only [plainFun, dite_eq_right h]

lemma plainFun_mono (n : ℕ) (a : Fin n → Fin n)
    (ha : Monotone a ∧ ∀ i, (a i).val ≤ i.val) :
    Monotone (plainFun n a) := by
  intro k1 k2 hle
  have hle' : k1.val ≤ k2.val := Fin.le_def.mp hle
  by_cases h1 : k1.val = 0
  · rw [Fin.le_def, plainFun_val_of_zero n a k1 h1]
    exact Nat.zero_le _
  · by_cases h2 : k2.val = 0
    · have hcon : k1.val = 0 := by
        omega
      exact absurd hcon h1
    · rw [Fin.le_def]
      rw [plainFun_val_of_ne n a k1 h1]
      rw [plainFun_val_of_ne n a k2 h2]
      have hmon : a ⟨k1.val - 1, by omega⟩ ≤ a ⟨k2.val - 1, by omega⟩ := by
        apply ha.1
        rw [Fin.le_def]
        simp only
        omega
      exact Fin.le_def.mp hmon

lemma plainFun_bound (n : ℕ) (a : Fin n → Fin n)
    (ha : Monotone a ∧ ∀ i, (a i).val ≤ i.val) (k : Fin (n + 1)) :
    (plainFun n a k).val ≤ k.val := by
  by_cases h : k.val = 0
  · rw [plainFun_val_of_zero n a k h]
    omega
  · rw [plainFun_val_of_ne n a k h]
    have hb := ha.2 ⟨k.val - 1, by omega⟩
    simp only at hb
    omega

end MetaMathlibExt
end
