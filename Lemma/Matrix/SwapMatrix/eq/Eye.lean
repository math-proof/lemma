import Initialize.Tactic.Attr.Basic
import Def.LinearAlgebra.Matrix.Permutation
import Mathlib.Algebra.Ring.Defs
open Matrix


@[path]
private lemma main
  [AddMonoidWithOne α]
-- given
  (i : Fin n) :
-- imply
  swapMatrix (α := α) i i = (1 : Matrix (Fin n) (Fin n) α) := by
-- proof
  ext a b
  simp only [swapMatrix, one_apply, of_apply]
  have hswap : Equiv.swap i i a = a := by
    simp [Equiv.swap_self]
  rw [hswap]
  simp only [KroneckerDelta]
  by_cases h : a = b <;> simp [h, Bool.toNat]


-- created on 2026-10-31
