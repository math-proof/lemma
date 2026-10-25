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
import Theorem.Combinatorics.Enumerative.FaultFree3xnTiling.Part15


namespace MetaMathlibExt

def ff3CodeHeadFilling {a : Finset (Fin 3)} {n : ℕ} (c : ff3Code a (n + 1)) :
    ff3ColumnFilling a (ff3ProfileRows (c.1 0)) := by
  simpa [ff3Incoming, ff3Outgoing] using c.2 0

def ff3CodeTail {a : Finset (Fin 3)} {n : ℕ} (c : ff3Code a (n + 1)) :
    ff3Code (ff3ProfileRows (c.1 0)) n := by
  refine ⟨Fin.tail c.1, fun j ↦ ?_⟩
  refine ⟨(c.2 j.succ).1, ?_⟩
  rw [ff3_incoming_tail (a := a) c.1 j, ff3_outgoing_tail c.1 j]
  exact (c.2 j.succ).property

def ff3CodeCons {a : Finset (Fin 3)} {n : ℕ} (p : ff3Profile)
    (f : ff3ColumnFilling a (ff3ProfileRows p))
    (c : ff3Code (ff3ProfileRows p) n) : ff3Code a (n + 1) := by
  refine ⟨Fin.cons p c.1, fun j ↦ Fin.cases ?_ (fun k ↦ ?_) j⟩
  · refine ⟨f.1, ?_⟩
    simpa [ff3Incoming, ff3Outgoing] using f.property
  · refine ⟨(c.2 k).1, ?_⟩
    simpa only [ff3_incoming_cons_succ, ff3_outgoing_cons_succ] using (c.2 k).property

end MetaMathlibExt
