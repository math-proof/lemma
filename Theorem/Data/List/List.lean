import Def.Data.List.Slice
import Def.Data.List.List.Part2
open Lean


@[simp]
theorem Function.getSliceFrom_apply (f : ℕ → α) (t k : ℕ) : f[t:] k = f (t + k) := rfl

theorem Function.getSliceFrom_def (f : ℕ → α) (t : ℕ) : f[t:] = fun k ↦ f (t + k) := rfl

