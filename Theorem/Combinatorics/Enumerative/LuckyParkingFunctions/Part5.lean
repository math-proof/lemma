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
import Def.Combinatorics.Enumerative.LuckyParkingFunctions.Part4


section

namespace MetaMathlibExt

lemma fiber_ge_le (n : ℕ) (a : Fin n → Fin n)
    (ha : Monotone a ∧ ∀ i, (a i).val ≤ i.val) (i0 : Fin n)
    (hi : a i0 = i0) (j : Fin n) (hle : i0.val ≤ j.val) :
    i0.val ≤ (a j).val := by
  have hij : i0 ≤ j := Fin.le_def.mpr hle
  have hmon : a i0 ≤ a j := ha.1 hij
  have hle2 : i0 ≤ a j := hi ▸ hmon
  exact Fin.le_def.mp hle2

lemma fiber_left_inv (n : ℕ) (i0 : Fin n) (x : Fiber n i0) :
    fiberFromProd n i0 (fiberToProd n i0 x) = x := by
  obtain ⟨⟨a, ha⟩, hi⟩ := x
  apply Subtype.ext
  apply Subtype.ext
  funext j
  apply Fin.ext
  simp only [fiberFromProd, fiberToProd]
  by_cases h : j.val < i0.val
  · have hJ := joinFun_val_of_lt n i0 (fiberToProd n i0 ⟨⟨a, ha⟩, hi⟩).1
      (fiberToProd n i0 ⟨⟨a, ha⟩, hi⟩).2 j h
    simp only [fiberToProd, splitLower] at hJ
    exact hJ
  · have hJ := joinFun_val_of_ge n i0 (fiberToProd n i0 ⟨⟨a, ha⟩, hi⟩).1
      (fiberToProd n i0 ⟨⟨a, ha⟩, hi⟩).2 j h
    simp only [fiberToProd, splitUpper] at hJ
    rw [hJ]
    have hle : i0.val ≤ j.val := by
      omega
    have heq :
        ∀ h' : i0.val + (j.val - i0.val) < n,
          (⟨i0.val + (j.val - i0.val), h'⟩ : Fin n) = j := by
      intro _
      apply Fin.ext
      simp only
      omega
    rw [heq _]
    have hle2 := fiber_ge_le n a ha i0 hi j hle
    omega

lemma fiber_right_inv (n : ℕ) (i0 : Fin n)
    (p : Park i0.val × Park (n - i0.val)) :
    fiberToProd n i0 (fiberFromProd n i0 p) = p := by
  obtain ⟨l, u⟩ := p
  apply Prod.ext
  · apply Subtype.ext
    funext j
    apply Fin.ext
    simp only [fiberToProd, fiberFromProd, splitLower]
    have h : (⟨j.val, by omega⟩ : Fin n).val < i0.val := j.isLt
    have hJ := joinFun_val_of_lt n i0 l u ⟨j.val, by omega⟩ h
    exact hJ
  · apply Subtype.ext
    funext k
    apply Fin.ext
    simp only [fiberToProd, fiberFromProd, splitUpper]
    have hneg : ¬ (⟨i0.val + k.val, by omega⟩ : Fin n).val < i0.val := by
      simp only
      omega
    have hJ := joinFun_val_of_ge n i0 l u ⟨i0.val + k.val, by omega⟩ hneg
    rw [hJ]
    have heq :
        ∀ h' : (i0.val + k.val) - i0.val < n - i0.val,
          (⟨(i0.val + k.val) - i0.val, h'⟩ : Fin (n - i0.val)) = k := by
      intro _
      apply Fin.ext
      simp only
      omega
    rw [heq _]
    omega

end MetaMathlibExt
end
