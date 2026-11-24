module
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.FaultFree3xnTiling.Part19


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MetaMathlibExt

theorem ff3_incoming_tail {a : Finset (Fin 3)} {n : ℕ}
    (p : Fin (n + 1) → ff3Profile) (j : Fin (n + 1)) :
    ff3Incoming (ff3ProfileRows (p 0)) (Fin.tail p) j = ff3Incoming a p j.succ := by
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · simp [ff3Incoming]
  · simp [ff3Incoming]
    congr

theorem ff3_outgoing_tail {n : ℕ} (p : Fin (n + 1) → ff3Profile)
    (j : Fin (n + 1)) : ff3Outgoing (Fin.tail p) j = ff3Outgoing p j.succ := by
  simp [ff3Outgoing, Fin.tail]

theorem ff3_incoming_cons_succ {a : Finset (Fin 3)} {n : ℕ} (p : ff3Profile)
    (q : Fin n → ff3Profile) (j : Fin (n + 1)) :
    ff3Incoming a (Fin.cons p q) j.succ = ff3Incoming (ff3ProfileRows p) q j := by
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · simp [ff3Incoming, Fin.cons]
  · simp [ff3Incoming, Fin.cons]

theorem ff3_outgoing_cons_succ {n : ℕ} (p : ff3Profile) (q : Fin n → ff3Profile)
    (j : Fin (n + 1)) : ff3Outgoing (Fin.cons p q) j.succ = ff3Outgoing q j := by
  simp [ff3Outgoing, Fin.cons]

end MetaMathlibExt
