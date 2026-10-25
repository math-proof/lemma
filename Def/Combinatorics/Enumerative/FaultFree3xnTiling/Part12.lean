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
import Abbrev.Combinatorics.Enumerative.FaultFree3xnTiling.Part6


namespace MetaMathlibExt

def ff3ColumnCount (a b : Finset (Fin 3)) :=
  Fintype.card (ff3ColumnFilling a b)

def ff3Matrix (R : Type) [Semiring R] : Matrix ff3Profile ff3Profile R := !![
  0, 1, 0, 1, 0, 1, 0;
  1, 0, 0, 1, 1, 0, 0;
  0, 0, 0, 1, 0, 0, 0;
  1, 1, 1, 0, 0, 0, 0;
  0, 1, 0, 0, 0, 0, 0;
  1, 0, 0, 0, 0, 0, 0;
  0, 0, 0, 0, 0, 0, 0]

def ff3Boundary (R : Type) [Semiring R] : ff3Profile → R :=
  ![2, 1, 1, 2, 1, 1, 1]

def ff3Path (a : Finset (Fin 3)) : ℕ → Type
  | 0 => ff3ColumnFilling a ∅
  | n + 1 => Σ p : ff3Profile,
      ff3ColumnFilling a (ff3ProfileRows p) × ff3Path (ff3ProfileRows p) n

@[instance_reducible] noncomputable def ff3PathFintypeDef :
    (a : Finset (Fin 3)) → (n : ℕ) → Fintype (ff3Path a n)
  | a, 0 => by
      change Fintype (ff3ColumnFilling a ∅)
      infer_instance
  | a, n + 1 => by
      change Fintype (Σ p : ff3Profile,
        ff3ColumnFilling a (ff3ProfileRows p) × ff3Path (ff3ProfileRows p) n)
      letI : ∀ p : ff3Profile, Fintype (ff3Path (ff3ProfileRows p) n) :=
        fun p ↦ ff3PathFintypeDef (ff3ProfileRows p) n
      infer_instance

end MetaMathlibExt
