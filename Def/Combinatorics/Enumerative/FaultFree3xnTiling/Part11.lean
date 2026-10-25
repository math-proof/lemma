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
import Theorem.Combinatorics.Enumerative.FaultFree3xnTiling.Part8


namespace MetaMathlibExt

noncomputable def ff3ProfileEquiv :
    ff3Profile ≃ {s : Finset (Fin 3) // s.Nonempty} :=
  Equiv.ofBijective ff3ProfileRows' ff3_profileRows_bijective

def ff3VerticalRows : Option (Fin 2) → Finset (Fin 3)
  | none => ∅
  | some r => {r.castSucc, r.succ}

end MetaMathlibExt
