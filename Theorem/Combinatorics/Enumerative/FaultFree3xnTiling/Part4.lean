module
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.FaultFree3xnTiling.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
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
