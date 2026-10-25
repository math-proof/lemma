/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/Paving.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
open scoped BigOperators

/-!
# Finite-dimensional paving reductions

This module packages the finite-support Marcus--Spielman--Srivastava bound and develops its
linear-algebraic consequences for paving Hermitian matrices.
-/


namespace MathlibExt.Analysis.CStarAlgebra.KadisonSinger

universe u v

open scoped Matrix.Norms.L2Operator in
/-- Finite-support form of the Marcus--Spielman--Srivastava random-vector bound. -/
def FiniteMSSBound : Prop :=
  ∀ (m : ℕ) (d : Type u) [Fintype d] [DecidableEq d] (s : Fin m → ℕ),
    (∀ i, 0 < s i) →
    ∀ (p : (i : Fin m) → Fin (s i) → ℝ)
      (v : (i : Fin m) → Fin (s i) → d → ℂ) (η : ℝ),
      0 ≤ η →
      (∀ i a, 0 ≤ p i a) →
      (∀ i, ∑ a, p i a = 1) →
      (∑ i, ∑ a, (p i a : ℂ) • Matrix.vecMulVec (v i a) (star (v i a)) = 1) →
      (∀ i, ∑ a, p i a * ∑ k, ‖v i a k‖ ^ 2 ≤ η) →
      ∃ ω : (i : Fin m) → Fin (s i),
        ‖∑ i, Matrix.vecMulVec (v i (ω i)) (star (v i (ω i)))‖ ≤
          (1 + Real.sqrt η) ^ 2

noncomputable def ksLiftVector {r d : ℕ} (a : Fin r) (u : Fin d → ℂ) :
    Fin r × Fin d → ℂ :=
  fun x ↦ if x.1 = a then (Real.sqrt r : ℂ) * u x.2 else 0

def ksMatrixEntryLM {m n : Type} (x : m) (y : n) : Matrix m n ℂ →ₗ[ℂ] ℂ :=
  (LinearMap.proj y : (n → ℂ) →ₗ[ℂ] ℂ).comp
    (LinearMap.proj x : Matrix m n ℂ →ₗ[ℂ] (n → ℂ))

noncomputable def ksPavingProj {n r : ℕ} (c : Fin n → Fin r) (j : Fin r) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i ↦ if c i = j then 1 else 0)

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

def ksColorGram {m d r : ℕ} (u : Fin m → Fin d → ℂ)
    (c : Fin m → Fin r) (j : Fin r) : Matrix (Fin d) (Fin d) ℂ :=
  ∑ i ∈ Finset.univ.filter (fun i ↦ c i = j), Matrix.vecMulVec (u i) (star (u i))

end MathlibExt.Analysis.CStarAlgebra.KadisonSinger
