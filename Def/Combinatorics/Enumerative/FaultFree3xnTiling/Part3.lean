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
public import Abbrev.Combinatorics.Enumerative.FaultFree3xnTiling.Part2

@[expose] public section

namespace MetaMathlibExt

def ff3Dominoes {n : ℕ} (T : Finset (Finset (TilingCell n))) :=
  T.filter fun d ↦ d.card = 2

def ff3Uncovered {n : ℕ} (D : Finset (Finset (TilingCell n))) :=
  Finset.univ.filter fun x ↦ ∀ d ∈ D, x ∉ d

def ff3Complete {n : ℕ} (D : Finset (Finset (TilingCell n))) :=
  D ∪ (ff3Uncovered D).image fun x ↦ {x}

end MetaMathlibExt
