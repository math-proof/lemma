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


namespace Analysis.CStarAlgebra.KadisonSinger

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

end Analysis.CStarAlgebra.KadisonSinger
