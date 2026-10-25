/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Theorem.Analysis.CStarAlgebra.KadisonSinger.Paving
open scoped BigOperators

/-!
# Finite-dimensional paving reductions

This module packages the finite-support Marcus--Spielman--Srivastava bound and develops its
linear-algebraic consequences for paving Hermitian matrices.
-/


namespace Analysis.CStarAlgebra.KadisonSinger

universe u v

noncomputable def ksPavingProj {n r : ℕ} (c : Fin n → Fin r) (j : Fin r) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i ↦ if c i = j then 1 else 0)

end Analysis.CStarAlgebra.KadisonSinger
