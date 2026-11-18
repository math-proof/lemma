module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Data.Finset.Max
public import Class.Algebra.BigOperators.Reduced

@[expose] public section

instance {α : Type*} [Fintype α] : Function.Reduce (α → ℝ) ℝ := ⟨fun v => ∑ b, v b⟩

instance {α γ δ : Type*} [Function.Reduce γ δ] : Function.Reduce (α → γ) (α → δ) :=
  ⟨fun v a => Function.Reduce.reduce (v a)⟩

