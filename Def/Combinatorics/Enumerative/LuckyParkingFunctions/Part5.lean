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
public import Theorem.Combinatorics.Enumerative.LuckyParkingFunctions.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LuckyParkingFunctions.lean -/
section

namespace MetaMathlibExt

def fiberEquiv (n : ℕ) (i0 : Fin n) :
    Fiber n i0 ≃ Park i0.val × Park (n - i0.val) where
  toFun := fiberToProd n i0
  invFun := fiberFromProd n i0
  left_inv := fiber_left_inv n i0
  right_inv := fiber_right_inv n i0

def markedFiberEquiv (n : ℕ) :
    Marked n ≃ Σ i0 : Fin n, Fiber n i0 where
  toFun x := ⟨x.2.1, ⟨x.1, x.2.2⟩⟩
  invFun y := ⟨y.2.1, ⟨y.1, y.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

def plainFun (n : ℕ) (a : Fin n → Fin n) :
    Fin (n + 1) → Fin (n + 1) :=
  fun k =>
    if h : k.val = 0 then ⟨0, by omega⟩
    else
      ⟨(a ⟨k.val - 1, by omega⟩).val, by
        have _h1 := (a ⟨k.val - 1, by omega⟩).isLt
        omega⟩

end MetaMathlibExt
end
