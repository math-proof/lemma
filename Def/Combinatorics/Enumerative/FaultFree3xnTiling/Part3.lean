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
import Abbrev.Combinatorics.Enumerative.FaultFree3xnTiling.Part2


namespace MetaMathlibExt

def ff3Dominoes {n : ℕ} (T : Finset (Finset (TilingCell n))) :=
  T.filter fun d ↦ d.card = 2

def ff3Uncovered {n : ℕ} (D : Finset (Finset (TilingCell n))) :=
  Finset.univ.filter fun x ↦ ∀ d ∈ D, x ∉ d

def ff3Complete {n : ℕ} (D : Finset (Finset (TilingCell n))) :=
  D ∪ (ff3Uncovered D).image fun x ↦ {x}

end MetaMathlibExt
