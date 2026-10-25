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
import Def.Combinatorics.Enumerative.LuckyParkingFunctions


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
