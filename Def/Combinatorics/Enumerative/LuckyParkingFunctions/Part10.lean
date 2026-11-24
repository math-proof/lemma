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
public import Theorem.Combinatorics.Enumerative.LuckyParkingFunctions.Part10


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean -/
section

namespace MetaMathlibExt

def unplainFun (n : ℕ) (b : Park (n + 1))
    (hNo : ∀ k : Fin (n + 1), 0 < k.val → b.1 k ≠ k) :
    Fin n → Fin n :=
  fun j =>
    ⟨(b.1 ⟨j.val + 1, by omega⟩).val, by
      have hpos :
          0 < (⟨j.val + 1, by omega⟩ : Fin (n + 1)).val := by
        simp only
        omega
      have hNe := hNo ⟨j.val + 1, by omega⟩ hpos
      have hb := b.2.2 ⟨j.val + 1, by omega⟩
      simp only at hb
      have hval_ne :
          (b.1 ⟨j.val + 1, by omega⟩).val ≠
            (⟨j.val + 1, by omega⟩ : Fin (n + 1)).val := by
        intro hEq
        exact hNe (Fin.ext hEq)
      simp only at hval_ne
      omega⟩

end MetaMathlibExt
end
