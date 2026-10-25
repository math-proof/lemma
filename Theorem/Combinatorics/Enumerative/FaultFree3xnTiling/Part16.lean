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
import Def.Combinatorics.Enumerative.FaultFree3xnTiling.Part20


namespace MetaMathlibExt

theorem ff3_codeCons_head_tail {a : Finset (Fin 3)} {n : ℕ}
    (c : ff3Code a (n + 1)) :
    ff3CodeCons (c.1 0) (ff3CodeHeadFilling c) (ff3CodeTail c) = c := by
  apply ff3_code_ext
  · exact Fin.cons_self_tail c.1
  · intro j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · rfl
    · rfl

theorem ff3_codeHeadFilling_cons {a : Finset (Fin 3)} {n : ℕ} (p : ff3Profile)
    (f : ff3ColumnFilling a (ff3ProfileRows p))
    (c : ff3Code (ff3ProfileRows p) n) :
    ff3CodeHeadFilling (ff3CodeCons p f c) = f := by
  apply Subtype.ext
  rfl

theorem ff3_codeTail_cons {a : Finset (Fin 3)} {n : ℕ} (p : ff3Profile)
    (f : ff3ColumnFilling a (ff3ProfileRows p))
    (c : ff3Code (ff3ProfileRows p) n) : ff3CodeTail (ff3CodeCons p f c) = c := by
  apply ff3_code_ext
  · funext j
    rfl
  · intro j
    rfl

end MetaMathlibExt
