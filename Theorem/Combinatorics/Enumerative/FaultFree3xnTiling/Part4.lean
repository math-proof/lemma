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
import Def.Combinatorics.Enumerative.FaultFree3xnTiling.Part5


namespace MetaMathlibExt

theorem ff3_edgeDomino_isDomino {n : ℕ} (e : ff3Edge n) :
    ff3IsDomino (ff3EdgeDomino e) := by
  rcases e with e | e
  · exact ff3_horizontal_isDomino e.1 e.2
  · exact ff3_vertical_isDomino e.1 e.2

theorem ff3_edgeDomino_injective {n : ℕ} :
    Function.Injective (@ff3EdgeDomino n) := by
  intro e f h
  rcases e with e | e <;> rcases f with f | f
  · exact congrArg Sum.inl (ff3_horizontal_injective h)
  · exact (ff3_horizontal_ne_vertical e.1 e.2 f.1 f.2 h).elim
  · exact (ff3_horizontal_ne_vertical f.1 f.2 e.1 e.2 h.symm).elim
  · exact congrArg Sum.inr (ff3_vertical_injective h)

end MetaMathlibExt
