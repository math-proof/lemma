/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Theorem.Analysis.CStarAlgebra.KadisonSinger.Paving.Part3

@[expose] public section

open scoped BigOperators

/-!
# Finite-dimensional paving reductions

This module packages the finite-support Marcus--Spielman--Srivastava bound and develops its
linear-algebraic consequences for paving Hermitian matrices.
-/


namespace Analysis.CStarAlgebra.KadisonSinger

universe u v

open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

def ksColorGram {m d r : ℕ} (u : Fin m → Fin d → ℂ)
    (c : Fin m → Fin r) (j : Fin r) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ i ∈ Finset.univ.filter (fun i ↦ c i = j), Matrix.vecMulVec (u i) (star (u i))

end Analysis.CStarAlgebra.KadisonSinger
