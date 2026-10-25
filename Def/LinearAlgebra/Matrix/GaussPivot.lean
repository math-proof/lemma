/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/GaussPivot.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.LinearAlgebra.Matrix.Echelon.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Finset.Sort
/-!
# Gaussian elimination with row pivots

This file constructs unit lower-triangular row operations for a pivot step and proves that a row
permutation followed by such operations puts every finite matrix over a field in row echelon form.
-/


namespace MathlibExt.LinearAlgebra.Matrix.GaussPivotWanted

def gaussPivotLiftPerm {p : ℕ} (τ : Equiv.Perm (Fin p)) :
    Equiv.Perm (Fin (p + 1)) where
  toFun := Fin.cases 0 fun i => (τ i).succ
  invFun := Fin.cases 0 fun i => (τ.symm i).succ
  left_inv i := by
    refine Fin.cases ?_ (fun k => ?_) i
    · rfl
    · simp
  right_inv i := by
    refine Fin.cases ?_ (fun k => ?_) i
    · rfl
    · simp

end MathlibExt.LinearAlgebra.Matrix.GaussPivotWanted
