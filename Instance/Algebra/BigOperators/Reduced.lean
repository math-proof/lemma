import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Finset.Max
import Class.Algebra.BigOperators.Reduced


instance : Function.Elementwise ℝ := ⟨fun f x => f x⟩

instance {α β : Type*} [Function.Elementwise β] : Function.Elementwise (α → β) :=
  ⟨fun f v a => Function.Elementwise.map f (v a)⟩

