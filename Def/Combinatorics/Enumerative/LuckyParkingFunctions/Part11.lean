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
public import Theorem.Combinatorics.Enumerative.LuckyParkingFunctions.Part11


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean -/
section

namespace MetaMathlibExt

def unmarkedFun (n : ℕ) (b : Park (n + 1)) (i0 : Fin n) :
    Fin n → Fin n :=
  fun j =>
    if h : j.val < i0.val then
      ⟨(b.1 ⟨j.val + 1, by omega⟩).val, by
        have hb := b.2.2 ⟨j.val + 1, by omega⟩
        simp only at hb
        have hi := i0.isLt
        omega⟩
    else
      ⟨(b.1 ⟨j.val + 1, by omega⟩).val - 1, by
        have hlt := (b.1 ⟨j.val + 1, by omega⟩).isLt
        omega⟩

end MetaMathlibExt
end
