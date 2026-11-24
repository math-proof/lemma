module
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring
public import Def.Combinatorics.Enumerative.FaultFree3xnTiling.Part20


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
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
