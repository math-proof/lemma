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
import Def.Combinatorics.Enumerative.LuckyParkingFunctions.Part10


section

namespace MetaMathlibExt

lemma embedPlain_unplain (n : ℕ) (b : Park (n + 1))
    (hNo : ∀ k : Fin (n + 1), 0 < k.val → b.1 k ≠ k) :
    embedPlain n ⟨unplainFun n b hNo, unplainFun_mono n b hNo,
      fun j => unplainFun_bound n b hNo j⟩ = b := by
  apply Subtype.ext
  funext k
  apply Fin.ext
  by_cases h0 : k.val = 0
  · have hL : ((embedPlain n ⟨unplainFun n b hNo, unplainFun_mono n b hNo,
        fun j => unplainFun_bound n b hNo j⟩).1 k).val = 0 :=
      plainFun_val_of_zero n _ k h0
    have hb := b.2.2 k
    omega
  · have hL : ((embedPlain n ⟨unplainFun n b hNo, unplainFun_mono n b hNo,
        fun j => unplainFun_bound n b hNo j⟩).1 k).val =
        (unplainFun n b hNo ⟨k.val - 1, by omega⟩).val :=
      plainFun_val_of_ne n _ k h0
    have heq : (⟨(⟨k.val - 1, by omega⟩ : Fin n).val + 1, by omega⟩ :
        Fin (n + 1)) = k := by
      apply Fin.ext
      simp only
      omega
    have hU : (unplainFun n b hNo ⟨k.val - 1, by omega⟩).val =
        (b.1 k).val := by
      have hrfl : (unplainFun n b hNo ⟨k.val - 1, by omega⟩).val =
          (b.1 ⟨(⟨k.val - 1, by omega⟩ : Fin n).val + 1, by omega⟩).val := rfl
      rw [hrfl, heq]
    rw [hL, hU]

end MetaMathlibExt
end
