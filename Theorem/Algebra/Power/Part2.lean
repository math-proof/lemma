import Mathlib.Data.Finset.Basic
import Instance.Algebra.Power.Part2


@[simp]
theorem FinsetPow.coe_apply [HPow α ℕ α] (γ : α) (s : Finset ℕ) (i : ℕ) :
    (γ ^ s : FinsetPow α) i = γ ^ i := rfl

