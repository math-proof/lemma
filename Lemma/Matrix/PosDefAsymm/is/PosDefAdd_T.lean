import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Lemma.Matrix.Dot_MulVecT.eq.Dot_MulVec
import sympy.matrices.dense
open scoped Matrix


@[main, mp, mpr]
private lemma main
  [Fintype α]
-- given
  (A : Matrix α α ℝ) :
-- imply
  PosDefAsymm A ↔ Matrix.PosDef (A + Aᵀ) := by
-- proof
  constructor
  case mp =>
    intro h
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · simpa using Matrix.isHermitian_add_transpose_self A
    · intro x hx
      rw [star_trivial, Matrix.add_mulVec, dotProduct_add]
      rw [Matrix.Dot_MulVecT.eq.Dot_MulVec]
      have := h.pd x hx
      linarith
  case mpr =>
    intro h
    constructor
    intro x hx
    have := Matrix.PosDef.dotProduct_mulVec_pos h hx
    rw [star_trivial, Matrix.add_mulVec, dotProduct_add] at this
    rw [Matrix.Dot_MulVecT.eq.Dot_MulVec] at this
    linarith


-- created on 2026-09-19
