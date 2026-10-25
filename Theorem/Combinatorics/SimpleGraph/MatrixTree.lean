/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/MatrixTree.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Def.Combinatorics.SimpleGraph.MatrixTree


section

namespace MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted

@[simp] theorem parentExt_root {V : Type*} [DecidableEq V] (root : V)
    (f : { v : V // v ≠ root } → V) : parentExt root f root = root := by
  simp [parentExt]

@[simp] theorem parentExt_apply {V : Type*} [DecidableEq V] (root : V)
    (f : { v : V // v ≠ root } → V) (v : { v : V // v ≠ root }) :
    parentExt root f (v : V) = f v := by
  simp [parentExt, v.2]

end MathlibExt.Combinatorics.SimpleGraph.MatrixTreeWanted
end
