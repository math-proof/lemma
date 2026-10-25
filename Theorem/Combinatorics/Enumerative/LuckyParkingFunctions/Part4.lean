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
import Def.Combinatorics.Enumerative.LuckyParkingFunctions.Part3


section

namespace MetaMathlibExt

lemma joinFun_val_of_lt (n : ℕ) (i0 : Fin n) (l : Park i0.val)
    (u : Park (n - i0.val)) (j : Fin n) (h : j.val < i0.val) :
    (joinFun n i0 l u j).val = (l.1 ⟨j.val, h⟩).val := by
  simp only [joinFun, dite_eq_left h]

lemma joinFun_val_of_ge (n : ℕ) (i0 : Fin n) (l : Park i0.val)
    (u : Park (n - i0.val)) (j : Fin n) (h : ¬ j.val < i0.val) :
    (joinFun n i0 l u j).val =
      (u.1 ⟨j.val - i0.val, by
        have _hj := j.isLt
        have _hi := i0.isLt
        omega⟩).val + i0.val := by
  simp only [joinFun, dite_eq_right h]

lemma joinFun_mono (n : ℕ) (i0 : Fin n) (l : Park i0.val)
    (u : Park (n - i0.val)) : Monotone (joinFun n i0 l u) := by
  intro j1 j2 hle
  have hle' : j1.val ≤ j2.val := Fin.le_def.mp hle
  by_cases h1 : j1.val < i0.val
  · by_cases h2 : j2.val < i0.val
    · rw [Fin.le_def]
      rw [joinFun_val_of_lt n i0 l u j1 h1]
      rw [joinFun_val_of_lt n i0 l u j2 h2]
      have hmon : l.1 ⟨j1.val, h1⟩ ≤ l.1 ⟨j2.val, h2⟩ := by
        apply l.2.1
        rw [Fin.le_def]
        simp only
        omega
      exact Fin.le_def.mp hmon
    · rw [Fin.le_def]
      rw [joinFun_val_of_lt n i0 l u j1 h1]
      rw [joinFun_val_of_ge n i0 l u j2 h2]
      have hlt : (l.1 ⟨j1.val, h1⟩).val < i0.val :=
        (l.1 ⟨j1.val, h1⟩).isLt
      omega
  · by_cases h2 : j2.val < i0.val
    · have hcon : j1.val < i0.val := lt_of_le_of_lt hle' h2
      exact absurd hcon h1
    · rw [Fin.le_def]
      rw [joinFun_val_of_ge n i0 l u j1 h1]
      rw [joinFun_val_of_ge n i0 l u j2 h2]
      have hle_sub : j1.val - i0.val ≤ j2.val - i0.val := by
        omega
      have hmon :
          u.1 ⟨j1.val - i0.val, by
            have _hj := j1.isLt
            have _hi := i0.isLt
            omega⟩ ≤
          u.1 ⟨j2.val - i0.val, by
            have _hj := j2.isLt
            have _hi := i0.isLt
            omega⟩ := by
        apply u.2.1
        rw [Fin.le_def]
        simp only
        exact hle_sub
      have h := Fin.le_def.mp hmon
      omega

lemma joinFun_bound (n : ℕ) (i0 : Fin n) (l : Park i0.val)
    (u : Park (n - i0.val)) (j : Fin n) :
    (joinFun n i0 l u j).val ≤ j.val := by
  by_cases h : j.val < i0.val
  · rw [joinFun_val_of_lt n i0 l u j h]
    have hb := l.2.2 ⟨j.val, h⟩
    simp only at hb
    exact hb
  · rw [joinFun_val_of_ge n i0 l u j h]
    have hb := u.2.2 ⟨j.val - i0.val, by
      have _hj := j.isLt
      have _hi := i0.isLt
      omega⟩
    simp only at hb
    omega

lemma joinFun_fixed (n : ℕ) (i0 : Fin n) (l : Park i0.val)
    (u : Park (n - i0.val)) : joinFun n i0 l u i0 = i0 := by
  have hneg : ¬ i0.val < i0.val := lt_irrefl _
  have hval := joinFun_val_of_ge n i0 l u i0 hneg
  have hpos : 0 < n - i0.val := by
    have _hi := i0.isLt
    omega
  have heq :
      (⟨i0.val - i0.val, by
        have _hj := i0.isLt
        have _hi := i0.isLt
        omega⟩ : Fin (n - i0.val)) =
        ⟨0, hpos⟩ := by
    apply Fin.ext
    simp only
    omega
  have hzero := park_zero_val (n - i0.val) u hpos
  apply Fin.ext
  rw [hval, heq, hzero]
  omega

end MetaMathlibExt
end
