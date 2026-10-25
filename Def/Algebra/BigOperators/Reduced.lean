import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Finset.Max
import Instance.Algebra.BigOperators.Reduced.Part3


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

