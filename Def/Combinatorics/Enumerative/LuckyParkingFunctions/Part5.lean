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
import Theorem.Combinatorics.Enumerative.LuckyParkingFunctions.Part5


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
