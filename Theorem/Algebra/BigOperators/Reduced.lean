import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Finset.Max
import Def.Algebra.BigOperators.Reduced


@[simp] theorem Function.exp_apply {α : Type*} (v : α → ℝ) (b : α) : v.exp b = Real.exp (v b) := rfl

@[simp] theorem Function.log_apply {α : Type*} (v : α → ℝ) (b : α) : v.log b = Real.log (v b) := rfl


@[simp] theorem Function.max_apply {α β : Type*} [Fintype β] [Nonempty β] (v : α → β → ℝ) (a : α) :
    v.max a = (v a).max := rfl


