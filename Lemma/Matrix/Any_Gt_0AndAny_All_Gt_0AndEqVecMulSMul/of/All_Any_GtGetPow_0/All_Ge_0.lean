import Mathlib.LinearAlgebra.Matrix.DotProduct
import Lemma.Matrix.Any_Gt_0AndAny_All_Gt_0AndEqMulVecSMul.of.All_Any_GtGetPow_0.All_Ge_0
import sympy.Basic

open Matrix
open scoped Matrix

@[path]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
  {A : Matrix S S ℝ}
-- given
  (h₀ : ∀ i j, 0 ≤ A i j)
  (h₁ : ∀ i j, ∃ n > 0, 0 < (A ^ n) i j) :
-- imply
  ∃ l : ℝ, 0 < l ∧ ∃ p : S → ℝ, (∀ k, 0 < p k) ∧ p ᵥ* A = l • p := by
-- proof
  obtain ⟨l, hl, p, hp, h⟩ := Any_Gt_0AndAny_All_Gt_0AndEqMulVecSMul.of.All_Any_GtGetPow_0.All_Ge_0 (A := Aᵀ) (fun i j => h₀ j i) (by
    intro i j
    obtain ⟨n, hn, h⟩ := h₁ j i
    refine ⟨n, hn, ?_⟩
    rwa [← Matrix.transpose_pow, Matrix.transpose_apply])
  refine ⟨l, hl, p, hp, ?_⟩
  rwa [← Matrix.mulVec_transpose]


-- created on 2026-09-29