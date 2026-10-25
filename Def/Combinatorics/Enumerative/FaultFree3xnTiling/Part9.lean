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
import Abbrev.Combinatorics.Enumerative.FaultFree3xnTiling.Part5


namespace MetaMathlibExt

def ff3ProfileRows : ff3Profile → Finset (Fin 3) := ![
  {0}, {1}, {0, 1}, {2}, {0, 2}, {1, 2}, {0, 1, 2}]

end MetaMathlibExt
