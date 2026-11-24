module
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.FaultFree3xnTiling.Part13


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
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
