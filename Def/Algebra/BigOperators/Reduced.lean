module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Data.Finset.Max
public import Class.Algebra.BigOperators.Reduced

@[expose] public section

/-- `v.exp = (fun b => (v b).exp)`, entrywise (py `Exp(v)`). -/
noncomputable def Function.exp {α β : Type*} [Function.Elementwise β] (v : α → β) : α → β :=
  fun b => Function.Elementwise.map Real.exp (v b)

/-- `v.log = (fun b => (v b).log)`, entrywise (py `Log(v)`). -/
noncomputable def Function.log {α β : Type*} [Function.Elementwise β] (v : α → β) : α → β :=
  fun b => Function.Elementwise.map Real.log (v b)

/-- `v.sum = ∑ b, v b` for a vector, and the row sums for a matrix (py `ReducedSum`). -/
def Function.sum {α β δ : Type*} [Function.Reduce (α → β) δ] (v : α → β) : δ :=
  Function.Reduce.reduce v

/-- `v.max = max_b v b` for a vector, and the row maxima (over the last axis) for a matrix (py `ReducedMax`). -/
def Function.max {α β δ : Type*} [Function.ReduceMax (α → β) δ] (v : α → β) : δ :=
  Function.ReduceMax.reduce v

