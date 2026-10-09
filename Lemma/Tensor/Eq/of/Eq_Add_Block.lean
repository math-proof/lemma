import Lemma.Tensor.ExpAdd_MulInfty.eq.Mul_Stack_Bool.rect
import sympy.Basic
open Tensor


/--
py: `Ξ = I + [[0, 1], [1, 0]]` (identity plus the off-diagonal block mask) gives
`exp(a + (Ξ - 1) * ∞) ≈ Ξ * exp(a)` (hyperreal masked exponential).
Here `Ξ i j = 1` if `i = j ∨ ¬(i < h ↔ j < h)`, else `0`.
-/
@[path]
private lemma mask.cross_attention
  {n h : ℕ}
-- given
  (Ξ : Tensor ℝ* [n, n])
  (a : Tensor ℝ [n, n])
  (h_Ξ : Ξ = [i < n] [j < n] (Bool.toNat (decide (i = j ∨ ¬(i.val < h ↔ j.val < h))))) :
-- imply
  let a : Tensor ℝ* [n, n] := a
  Exp.exp (a + (Ξ - 1) * ∞) ≈ Ξ * exp a := by
-- proof
  intro a'
  subst h_Ξ
  rw [mul_comm]
  exact ExpAdd_MulInfty.eq.Mul_Stack_Bool.rect (fun (i : Fin n) (j : Fin n) => decide (i = j ∨ ¬(i.val < h ↔ j.val < h))) a


-- created on 2026-09-27