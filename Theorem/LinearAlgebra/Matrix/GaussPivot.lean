/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/GaussPivot.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.LinearAlgebra.Matrix.Echelon.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Data.Finset.Sort
import Def.LinearAlgebra.Matrix.GaussPivot
/-!
# Gaussian elimination with row pivots

This file constructs unit lower-triangular row operations for a pivot step and proves that a row
permutation followed by such operations puts every finite matrix over a field in row echelon form.
-/


namespace MathlibExt.LinearAlgebra.Matrix.GaussPivotWanted

@[simp] theorem gaussPivotLiftPerm_zero {p : ℕ} (τ : Equiv.Perm (Fin p)) :
    gaussPivotLiftPerm τ 0 = 0 := rfl

@[simp] theorem gaussPivotLiftPerm_succ {p : ℕ} (τ : Equiv.Perm (Fin p))
    (i : Fin p) : gaussPivotLiftPerm τ i.succ = (τ i).succ := rfl

end MathlibExt.LinearAlgebra.Matrix.GaussPivotWanted
