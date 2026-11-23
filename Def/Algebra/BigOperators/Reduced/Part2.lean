module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Data.Finset.Max
public import Theorem.Algebra.BigOperators.Reduced

@[expose] public section

/-- py `ReducedArgMax(v)`: the FIRST index attaining the maximum of `v`; py's `_eval_ReducedArgMax`
scans left-to-right keeping only strict improvements `val > M`, so on ties the earliest index wins.
(Named after py since Mathlib's `Function.argmax` is the well-founded variant.) -/
noncomputable def ReducedArgMax {α : Type*} [LinearOrder α] [Fintype α] [Nonempty α] (v : α → ℝ) :
    α :=
  (Finset.univ.filter fun i => ∀ j, v j ≤ v i).min' (by
    obtain ⟨i, hi⟩ := Finite.exists_max v
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩)

