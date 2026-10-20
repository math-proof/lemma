import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Matrix.VanDerWaerden
open Matrix
open MathlibExt.LinearAlgebra.Matrix.VanDerWaerdenWanted


/--
[van_der_waerden_permanent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/VanDerWaerden.lean)
-/
@[path]
private lemma van_der_waerden_permanent_eq
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) ℝ}
-- given
  (hn : 0 < n)
  (hA : A ∈ doublyStochastic ℝ (Fin n)) :
-- imply
  ((n.factorial : ℝ) / (n : ℝ) ^ n) ≤ A.permanent := by
-- proof
  apply MathlibExt.LinearAlgebra.Matrix.VanDerWaerdenWanted.van_der_waerden_permanent hn A hA


-- created on 2026-10-20
