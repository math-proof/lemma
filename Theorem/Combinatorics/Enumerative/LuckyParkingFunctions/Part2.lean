/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean -/

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
public import Def.Combinatorics.Enumerative.LuckyParkingFunctions

@[expose] public section

section

namespace MetaMathlibExt

lemma splitLower_mono (n : ℕ) (a : Fin n → Fin n) (ha : Monotone a ∧ ∀ i, (a i).val ≤ i.val)
    (i0 : Fin n) : Monotone (splitLower n a ha i0) := by
  intro j k hjk
  have hjk' : j.val ≤ k.val := Fin.le_def.mp hjk
  change (splitLower n a ha i0 j).val ≤ (splitLower n a ha i0 k).val
  simp only [splitLower]
  have hmon : a ⟨j.val, by omega⟩ ≤ a ⟨k.val, by omega⟩ := by
    apply ha.1
    rw [Fin.le_def]
    simp only
    exact hjk'
  exact Fin.le_def.mp hmon

lemma splitLower_bound (n : ℕ) (a : Fin n → Fin n)
    (ha : Monotone a ∧ ∀ i, (a i).val ≤ i.val) (i0 : Fin n)
    (j : Fin i0.val) : (splitLower n a ha i0 j).val ≤ j.val := by
  simp only [splitLower]
  have h := ha.2 ⟨j.val, by omega⟩
  simp only at h ⊢
  omega

end MetaMathlibExt
end
