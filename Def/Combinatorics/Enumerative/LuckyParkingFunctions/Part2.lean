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
public import Theorem.Combinatorics.Enumerative.LuckyParkingFunctions.Part2

@[expose] public section

section

namespace MetaMathlibExt

def splitUpper (n : ℕ) (a : Fin n → Fin n) (ha : Monotone a ∧ ∀ i, (a i).val ≤ i.val)
    (i0 : Fin n) (hi : a i0 = i0) : Fin (n - i0.val) → Fin (n - i0.val) :=
  fun k => ⟨(a ⟨i0.val + k.val, by omega⟩).val - i0.val, by
    have hmon : i0 ≤ a ⟨i0.val + k.val, by omega⟩ := by
      calc i0 = a i0 := hi.symm
        _ ≤ a ⟨i0.val + k.val, by omega⟩ := ha.1 (by rw [Fin.le_def]; simp only; omega)
    have hle : i0.val ≤ (a ⟨i0.val + k.val, by omega⟩).val := Fin.le_def.mp hmon
    have hlt : (a ⟨i0.val + k.val, by omega⟩).val < n := (a _).isLt
    omega⟩

end MetaMathlibExt
end
