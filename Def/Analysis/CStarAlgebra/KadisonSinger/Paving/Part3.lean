/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Abbrev.Analysis.CStarAlgebra.KadisonSinger.Paving

@[expose] public section

open scoped BigOperators

/-!
# Finite-dimensional paving reductions

This module packages the finite-support Marcus--Spielman--Srivastava bound and develops its
linear-algebraic consequences for paving Hermitian matrices.
-/


namespace Analysis.CStarAlgebra.KadisonSinger

universe u v

noncomputable def ksLiftVector {r d : ℕ} (a : Fin r) (u : Fin d → ℂ) :
    Fin r × Fin d → ℂ :=
  fun x ↦ if x.1 = a then (Real.sqrt r : ℂ) * u x.2 else 0

def ksMatrixEntryLM {m n : Type} (x : m) (y : n) : Matrix m n ℂ →ₗ[ℂ] ℂ :=
  (LinearMap.proj y : (n → ℂ) →ₗ[ℂ] ℂ).comp
    (LinearMap.proj x : Matrix m n ℂ →ₗ[ℂ] (n → ℂ))

end Analysis.CStarAlgebra.KadisonSinger
