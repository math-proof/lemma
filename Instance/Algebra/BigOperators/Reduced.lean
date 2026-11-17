module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Data.Finset.Max
public import Class.Algebra.BigOperators.Reduced

@[expose] public section

instance : Function.Elementwise ℝ := ⟨fun f x => f x⟩

instance {α β : Type*} [Function.Elementwise β] : Function.Elementwise (α → β) :=
  ⟨fun f v a => Function.Elementwise.map f (v a)⟩

