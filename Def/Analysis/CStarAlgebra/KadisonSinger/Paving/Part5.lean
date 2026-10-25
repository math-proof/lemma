/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Theorem.Analysis.CStarAlgebra.KadisonSinger.Paving.Part2
open scoped BigOperators

/-!
# Finite-dimensional paving reductions

This module packages the finite-support Marcus--Spielman--Srivastava bound and develops its
linear-algebraic consequences for paving Hermitian matrices.
-/


namespace Analysis.CStarAlgebra.KadisonSinger

universe u v

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

noncomputable def ksBlockEmbedding {r d : ℕ}
    (j : Fin r) : Matrix (Fin r × Fin d) (Fin d) ℂ :=
  fun x a => if x = (j, a) then 1 else 0

def ksBlock {r d : ℕ}
    (M : Matrix (Fin r × Fin d) (Fin r × Fin d) ℂ) (j : Fin r) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun a b => M (j, a) (j, b)

noncomputable def ksMatrixCLM {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ m :=
  (Matrix.toEuclideanLin (m := m) (n := n) (𝕜 := ℂ)).trans LinearMap.toContinuousLinearMap A

noncomputable def ksOperatorNorm {m n : Type} [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) : ℝ :=
  ‖ksMatrixCLM A‖

end Analysis.CStarAlgebra.KadisonSinger
