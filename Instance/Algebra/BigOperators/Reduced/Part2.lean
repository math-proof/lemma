import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Finset.Max
import Class.Algebra.BigOperators.Reduced.Part2


instance {α : Type*} [Fintype α] : Function.Reduce (α → ℝ) ℝ := ⟨fun v => ∑ b, v b⟩

instance {α γ δ : Type*} [Function.Reduce γ δ] : Function.Reduce (α → γ) (α → δ) :=
  ⟨fun v a => Function.Reduce.reduce (v a)⟩

