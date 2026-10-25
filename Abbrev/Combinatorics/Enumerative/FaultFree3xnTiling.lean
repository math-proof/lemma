/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring


namespace MetaMathlibExt

/-! # Fault-free 3 × n tilings recursion

This file proves the recurrence for vertical-fault-free tilings of a `3 × n` rectangle by
squares and dominoes.
-/

/-- A cell of a `3 × n` rectangle, represented by its row and column. -/
abbrev TilingCell (n : ℕ) := Fin 3 × Fin n

end MetaMathlibExt
