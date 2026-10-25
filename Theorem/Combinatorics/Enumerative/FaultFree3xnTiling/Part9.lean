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
import Def.Combinatorics.Enumerative.FaultFree3xnTiling.Part13


namespace MetaMathlibExt

theorem ff3_outgoing_castSucc {n : ℕ} (p : Fin n → ff3Profile) (k : Fin n) :
    ff3Outgoing p k.castSucc = ff3ProfileRows (p k) := by
  simp only [ff3Outgoing, Fin.val_castSucc, k.isLt, ↓reduceDIte]

theorem ff3_incoming_succ {n : ℕ} (a : Finset (Fin 3))
    (p : Fin n → ff3Profile) (k : Fin n) :
    ff3Incoming a p k.succ = ff3ProfileRows (p k) := by
  simp only [ff3Incoming, Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false,
    ↓reduceDIte]
  congr

end MetaMathlibExt
