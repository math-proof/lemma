module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Data.Finset.Max
public import Class.Algebra.BigOperators.Reduced
@[expose] public section

instance {α : Type*} [Fintype α] [Nonempty α] : Function.ReduceMax (α → ℝ) ℝ :=
  ⟨fun v => Finset.univ.sup' Finset.univ_nonempty v⟩

instance {α γ δ : Type*} [Function.ReduceMax γ δ] : Function.ReduceMax (α → γ) (α → δ) :=
  ⟨fun v a => Function.ReduceMax.reduce (v a)⟩

/-- Broadcasting: `(f + c) a = f a + c`, e.g. a matrix `G : α → β → ℝ` plus a vector `v : β → ℝ`
is `fun a b => G a b + v b` (py `G + v`). -/
instance {α γ : Type*} [Add γ] : HAdd (α → γ) γ (α → γ) := ⟨fun f c a => f a + c⟩

