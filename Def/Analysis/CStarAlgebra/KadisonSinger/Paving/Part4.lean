/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Theorem.Analysis.CStarAlgebra.KadisonSinger.Paving

@[expose] public section

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
