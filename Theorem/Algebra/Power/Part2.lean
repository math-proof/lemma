module

public import Mathlib.Data.Finset.Basic
public import Structure.Algebra.Power

@[expose] public section

namespace FinsetPow

public instance [HPow α ℕ α] : CoeFun (FinsetPow α) (fun _ => ℕ → α) where
  coe p := fun i => p.base ^ i

end FinsetPow

public instance [HPow α ℕ α] : HPow α (Finset ℕ) (FinsetPow α) where
  hPow base support := ⟨base, support⟩

@[simp]
public theorem FinsetPow.coe_apply [HPow α ℕ α] (γ : α) (s : Finset ℕ) (i : ℕ) :
    (γ ^ s : FinsetPow α) i = γ ^ i := rfl
