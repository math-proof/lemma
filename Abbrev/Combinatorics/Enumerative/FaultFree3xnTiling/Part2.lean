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
public import Def.Combinatorics.Enumerative.FaultFree3xnTiling.Part2

@[expose] public section


namespace MetaMathlibExt

abbrev ff3FaultFreeTilings (n : ℕ) :=
  {T : Finset (Finset (TilingCell n)) //
    IsSquareDominoTiling T ∧ IsVerticalFaultFree T}

abbrev ff3FaultFreeMatchings (n : ℕ) :=
  {D : Finset (Finset (TilingCell n)) //
    ff3IsMatching D ∧ IsVerticalFaultFree D}

end MetaMathlibExt
