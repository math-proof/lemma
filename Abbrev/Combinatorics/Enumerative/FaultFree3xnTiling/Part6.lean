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
import Def.Combinatorics.Enumerative.FaultFree3xnTiling.Part11


namespace MetaMathlibExt

abbrev ff3ColumnFilling (a b : Finset (Fin 3)) :=
  {v : Option (Fin 2) //
    Disjoint a b ∧
      Disjoint a (ff3VerticalRows v) ∧ Disjoint b (ff3VerticalRows v)}

end MetaMathlibExt
