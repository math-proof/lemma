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
import Def.Combinatorics.Enumerative.FaultFree3xnTiling.Part19


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
