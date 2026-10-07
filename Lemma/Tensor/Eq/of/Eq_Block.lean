import Lemma.Tensor.ExpAdd_MulInfty.eq.Mul_Stack_Bool.rect
import sympy.Basic
open Tensor


@[main]
private lemma double_integer_embedding
  {h m i : ℕ}
  {AX : ℕ → Fin (m + m) → ℝ}
  {AL AH : ℕ → Fin m → ℝ}
-- given
  (h₀ : h > 0)
  (h₁ : ∀ i, AX i = Fin.append (AL (i / h % h)) (AH (i % h))) :
-- imply
  AX (i + h * h) = AX i := by
-- proof
  rw [h₁, h₁, Nat.add_mul_div_right _ _ h₀, Nat.add_mod_right, Nat.add_mul_mod_self_right]


/--
py: `Ξ = [[0, 1], [1, 0]]` (block matrix, zeros on the `h × h` and `(n-h) × (n-h)` diagonal blocks,
ones elsewhere) gives `exp(a + (Ξ - 1) * ∞) ≈ Ξ * exp(a)` (hyperreal masked exponential).
Here `Ξ i j = 0` if `i < h ↔ j < h`, else `1`.
-/
@[main]
private lemma mask.cross_attention
  {n h : ℕ}
-- given
  (Ξ : Tensor ℝ* [n, n])
  (a : Tensor ℝ [n, n])
  (h_Ξ : Ξ = [i < n] [j < n] (Bool.toNat (decide ¬(i.val < h ↔ j.val < h)))) :
-- imply
  let a : Tensor ℝ* [n, n] := a
  Exp.exp (a + (Ξ - 1) * ∞) ≈ Ξ * exp a := by
-- proof
  intro a'
  subst h_Ξ
  rw [mul_comm]
  exact ExpAdd_MulInfty.eq.Mul_Stack_Bool.rect (fun (i : Fin n) (j : Fin n) => decide ¬(i.val < h ↔ j.val < h)) a


-- created on 2022-02-18
-- updated on 2026-09-27