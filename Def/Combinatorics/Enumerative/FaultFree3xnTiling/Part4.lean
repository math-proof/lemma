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
import Theorem.Combinatorics.Enumerative.FaultFree3xnTiling.Part2


namespace MetaMathlibExt

def ff3_tilingMatchingEquiv (n : ℕ) :
    ff3FaultFreeTilings n ≃ ff3FaultFreeMatchings n where
  toFun T := ⟨ff3Dominoes T, ff3_dominoes_matching T.property.1,
    ff3_dominoes_faultFree T.property.1.1 T.property.2⟩
  invFun D := ⟨ff3Complete D, ff3_complete_tiling D.property.1,
    ff3_complete_faultFree D.property.2⟩
  left_inv T := Subtype.ext (ff3_complete_dominoes T.property.1)
  right_inv D := Subtype.ext (ff3_dominoes_complete D.property.1)

def ff3HorizontalDomino {n : ℕ} (r : Fin 3) (k : Fin n) :
    Finset (TilingCell (n + 1)) :=
  {(r, k.castSucc), (r, k.succ)}

def ff3VerticalDomino {n : ℕ} (r : Fin 2) (k : Fin (n + 1)) :
    Finset (TilingCell (n + 1)) :=
  {(r.castSucc, k), (r.succ, k)}

end MetaMathlibExt
