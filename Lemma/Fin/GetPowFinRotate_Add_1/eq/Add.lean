import sympy.matrices.block_swap
import sympy.Basic
open Equiv Matrix.BlockSwap


@[path]
private lemma main
-- given
  (N a : ℕ)
  (v : Fin (N + 1)) :
-- imply
  (((finRotate (N + 1)) ^ a) v : ℕ) = (v + a) % (N + 1) := by
-- proof
  induction a with
  | zero => simp [Nat.mod_eq_of_lt v.2]
  | succ a ih =>
    rw [pow_succ', Perm.mul_apply, finRotate_apply, Fin.val_add, ih]
    simp only [Fin.val_one', Nat.add_mod_mod, Nat.mod_add_mod, Nat.add_assoc]


-- created on 2026-10-07
