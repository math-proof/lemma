import Mathlib
import Theorem.Analysis.Misc.erdos_613
open Classical
open scoped BigOperators


namespace PikhurkoN5

open V

deriving instance Fintype for V

/-- An explicit equivalence showing {name}`V` has 2+5+3+5+1 = 16 elements. -/
def VEquiv :
    V ≃ ((((Fin 2 ⊕ Fin 5) ⊕ Fin 3) ⊕ Fin 5) ⊕ Unit) where
  toFun
  | A1 i  => Sum.inl (Sum.inl (Sum.inl (Sum.inl i)))
  | B1 j  => Sum.inl (Sum.inl (Sum.inl (Sum.inr j)))
  | A2 i  => Sum.inl (Sum.inl (Sum.inr i))
  | B2 j  => Sum.inl (Sum.inr j)
  | apex  => Sum.inr ()
  invFun
  | Sum.inl (Sum.inl (Sum.inl (Sum.inl i))) => A1 i
  | Sum.inl (Sum.inl (Sum.inl (Sum.inr j))) => B1 j
  | Sum.inl (Sum.inl (Sum.inr i))            => A2 i
  | Sum.inl (Sum.inr j)                      => B2 j
  | Sum.inr ()                               => apex
  left_inv v := by cases v <;> grind
  right_inv w := by cases w <;> grind

end PikhurkoN5
