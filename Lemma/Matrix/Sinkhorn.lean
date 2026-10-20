import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Matrix.Sinkhorn
open Matrix
open MathlibExt.LinearAlgebra.Matrix.SinkhornWanted


/--
[sinkhorn_scaling](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/Sinkhorn.lean)
-/
@[path]
private lemma sinkhorn_scaling_eq
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) ℝ}
-- given
  (hn : 0 < n)
  (hA : ∀ i j, 0 < A i j) :
-- imply
  ∃ (r c : Fin n → ℝ), (∀ i, 0 < r i) ∧ (∀ j, 0 < c j) ∧
    (fun i j => r i * A i j * c j) ∈ doublyStochastic ℝ (Fin n) := by
-- proof
  apply MathlibExt.LinearAlgebra.Matrix.SinkhornWanted.sinkhorn_scaling hn A hA


-- created on 2026-10-20
