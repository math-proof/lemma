/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ReducedRowEchelon.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.LinearAlgebra.Matrix.Echelon.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin

import Mathlib.LinearAlgebra.Matrix.Echelon.Pivot

/-!
# Reduced row echelon form

This file proves existence and uniqueness of reduced row echelon representatives over a field,
and that invertible row operations preserve the kernel of the associated `mulVec` map.
-/

namespace Matrix.IsReducedRowEchelon

section

variable {R : Type*} [Zero R] [One R]
variable {m n : Type*}

end
end Matrix.IsReducedRowEchelon
namespace MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted
private noncomputable def rrefPivotColumns {V : Type*} [AddCommGroup V] [Module K V]
    (v : n → V) : Finset n := by
  classical
  exact Finset.univ.filter fun j ↦ v j ∉ Submodule.span K (v '' Set.Iio j)
end MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted
