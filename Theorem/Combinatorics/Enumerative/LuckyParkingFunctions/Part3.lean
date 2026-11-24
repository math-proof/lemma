module
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Rat.Star
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.LuckyParkingFunctions.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean -/
section

namespace MetaMathlibExt

lemma splitUpper_mono (n : ℕ) (a : Fin n → Fin n) (ha : Monotone a ∧ ∀ i, (a i).val ≤ i.val)
    (i0 : Fin n) (hi : a i0 = i0) : Monotone (splitUpper n a ha i0 hi) := by
  intro k1 k2 hle
  have hle' : k1.val ≤ k2.val := Fin.le_def.mp hle
  change (splitUpper n a ha i0 hi k1).val ≤ (splitUpper n a ha i0 hi k2).val
  simp only [splitUpper]
  have hmon : a ⟨i0.val + k1.val, by omega⟩ ≤ a ⟨i0.val + k2.val, by omega⟩ := by
    apply ha.1
    rw [Fin.le_def]
    simp only
    omega
  have h := Fin.le_def.mp hmon
  omega

lemma splitUpper_bound (n : ℕ) (a : Fin n → Fin n)
    (ha : Monotone a ∧ ∀ i, (a i).val ≤ i.val) (i0 : Fin n)
    (hi : a i0 = i0) (k : Fin (n - i0.val)) :
    (splitUpper n a ha i0 hi k).val ≤ k.val := by
  simp only [splitUpper]
  have h := ha.2 ⟨i0.val + k.val, by omega⟩
  simp only at h ⊢
  omega

end MetaMathlibExt
end
