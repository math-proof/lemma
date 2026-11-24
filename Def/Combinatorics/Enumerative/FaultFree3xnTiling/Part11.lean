module
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Int.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.FaultFree3xnTiling.Part8


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FaultFree3xnTiling.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MetaMathlibExt

noncomputable def ff3ProfileEquiv :
    ff3Profile ≃ {s : Finset (Fin 3) // s.Nonempty} :=
  Equiv.ofBijective ff3ProfileRows' ff3_profileRows_bijective

def ff3VerticalRows : Option (Fin 2) → Finset (Fin 3)
  | none => ∅
  | some r => {r.castSucc, r.succ}

end MetaMathlibExt
