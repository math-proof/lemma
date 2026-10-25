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
import Def.Combinatorics.Enumerative.FaultFree3xnTiling.Part2


namespace MetaMathlibExt

abbrev ff3FaultFreeTilings (n : ℕ) :=
  {T : Finset (Finset (TilingCell n)) //
    IsSquareDominoTiling T ∧ IsVerticalFaultFree T}

abbrev ff3FaultFreeMatchings (n : ℕ) :=
  {D : Finset (Finset (TilingCell n)) //
    ff3IsMatching D ∧ IsVerticalFaultFree D}

end MetaMathlibExt
