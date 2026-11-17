module

public import Def.Data.List.Slice
public import Def.Data.List.List.Basic
open Lean

public section

@[simp]
theorem Function.getSliceFrom_apply (f : ℕ → α) (t k : ℕ) : f[t:] k = f (t + k) := rfl

theorem Function.getSliceFrom_def (f : ℕ → α) (t : ℕ) : f[t:] = fun k ↦ f (t + k) := rfl

