module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Data.Finset.Max
public import Def.Algebra.BigOperators.Reduced
public import Instance.Algebra.BigOperators.Reduced
public import Instance.Algebra.BigOperators.Reduced.Part2
public import Instance.Algebra.BigOperators.Reduced.Part3

public section

@[simp] theorem Function.exp_apply {α : Type*} (v : α → ℝ) (b : α) : v.exp b = Real.exp (v b) := rfl

@[simp] theorem Function.log_apply {α : Type*} (v : α → ℝ) (b : α) : v.log b = Real.log (v b) := rfl


@[simp] theorem Function.max_apply {α β : Type*} [Fintype β] [Nonempty β] (v : α → β → ℝ) (a : α) :
    v.max a = (v a).max := rfl


