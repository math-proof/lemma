/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.NumberTheory.LegendreSymbol.Basic
import Def.NumberTheory.QuadraticForms.ThreeSquares
import Lemma.Nat.QuadraticForms.ThreeSquares
import Mathlib.Algebra.Quaternion
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.FieldTheory.Finite.Basic
import Theorem.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion.Part8


namespace MetaMathlibExt

noncomputable def r3legImageRep (p n : ℕ) (π : Quaternion ℤ) :
    Finset r3legIntVec := by
  classical
  exact (r3legRep (p ^ 2 * n)).filter
    (fun y => r3legVecDvd ((p : ℤ) ^ 2) (r3legPhi (star π) y))

end MetaMathlibExt
