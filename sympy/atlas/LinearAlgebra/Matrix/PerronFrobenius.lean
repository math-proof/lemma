/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/PerronFrobenius.lean -/

import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Matrix

section
open Matrix

namespace MathlibExt.LinearAlgebra.Matrix.PerronFrobeniusWanted

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Coercion of a real matrix to complex via `Complex.ofReal`. -/
noncomputable def toComplexMatrix (A : Matrix n n ℝ) : Matrix n n ℂ :=
  A.map Complex.ofReal

/-- The Collatz–Wielandt value of a vector: the least ratio `(A x)_i / x_i`. -/
private noncomputable def cwValue (A : Matrix n n ℝ) (z : n → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => A.mulVec z i / z i)
end MathlibExt.LinearAlgebra.Matrix.PerronFrobeniusWanted
