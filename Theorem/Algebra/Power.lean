import Mathlib.Data.Finset.Basic
import Instance.Algebra.Power


@[simp]
theorem Function.hPow_apply {α : Type u} [HPow α Nat α] (γ : α) (f : Nat → Nat) (k : Nat) :
    (γ ^ f) k = γ ^ f k := rfl

