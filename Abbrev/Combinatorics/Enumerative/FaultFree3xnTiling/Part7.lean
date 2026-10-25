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
import Theorem.Combinatorics.Enumerative.FaultFree3xnTiling.Part9


namespace MetaMathlibExt

abbrev ff3Code (a : Finset (Fin 3)) (n : ℕ) :=
  Σ p : Fin n → ff3Profile,
    ∀ j : Fin (n + 1), ff3ColumnFilling (ff3Incoming a p j) (ff3Outgoing p j)

end MetaMathlibExt
