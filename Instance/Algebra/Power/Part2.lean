import Mathlib.Data.Finset.Basic
import Structure.Algebra.Power


namespace FinsetPow

instance [HPow α ℕ α] : CoeFun (FinsetPow α) (fun _ => ℕ → α) where
  coe p := fun i => p.base ^ i

end FinsetPow

instance [HPow α ℕ α] : HPow α (Finset ℕ) (FinsetPow α) where
  hPow base support := ⟨base, support⟩

