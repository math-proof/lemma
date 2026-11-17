/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring

@[expose] public section


namespace MetaMathlibExt

/-! # Fault-free 3 × n tilings recursion

This file proves the recurrence for vertical-fault-free tilings of a `3 × n` rectangle by
squares and dominoes.
-/

/-- A cell of a `3 × n` rectangle, represented by its row and column. -/
abbrev TilingCell (n : ℕ) := Fin 3 × Fin n

end MetaMathlibExt
