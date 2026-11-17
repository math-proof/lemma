module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.Pi
public import Def.Data.List.List.Basic
public import Instance.Analysis.Real.Numbers
public import Notation.Fun

@[expose] public section

open scoped ENNReal.ToRealCoe


/-- `x[a:b]` for a family of random variables `x i : Ω → α`: the random vector
`ω ↦ (x a ω, …, x (b-1) ω)`. -/
instance {Ω α : Type*} : FunSlice (Ω → α) where
  Out s := Ω → Fin (s.stop.toNat - s.start.toNat) → α
  slice x s := fun ω i => x (i.val + s.start.toNat) ω
