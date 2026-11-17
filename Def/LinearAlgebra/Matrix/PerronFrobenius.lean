/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/PerronFrobenius.lean -/

module

public import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Instances.Matrix

@[expose] public section

section

open Matrix

namespace MathlibExt.LinearAlgebra.Matrix.PerronFrobeniusWanted

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- Coercion of a real matrix to complex via `Complex.ofReal`. -/
noncomputable def toComplexMatrix (A : Matrix n n ℝ) : Matrix n n ℂ :=
  A.map Complex.ofReal

/-- The Collatz–Wielandt value of a vector: the least ratio `(A x)_i / x_i`. -/
noncomputable def cwValue (A : Matrix n n ℝ) (z : n → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => A.mulVec z i / z i)

end MathlibExt.LinearAlgebra.Matrix.PerronFrobeniusWanted
end
