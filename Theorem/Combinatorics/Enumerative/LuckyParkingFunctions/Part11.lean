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
public import Def.Combinatorics.Enumerative.LuckyParkingFunctions.Part10


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean -/
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
