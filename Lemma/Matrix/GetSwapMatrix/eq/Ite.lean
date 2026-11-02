import Initialize.Tactic.Attr.Basic
import Def.LinearAlgebra.Matrix.Permutation
import Mathlib.Algebra.Ring.Defs


@[path]
private lemma main
  [AddMonoidWithOne α]
-- given
  (i₀ j₀ i j : Fin n) :
-- imply
  (swapMatrix (α := α) i₀ j₀) i j =
    if i = j₀ then
      (KroneckerDelta j i₀ : α)
    else if i = i₀ then
      (KroneckerDelta j j₀ : α)
    else
      (KroneckerDelta j i : α) := by
-- proof
  simp only [swapMatrix, Matrix.of_apply, Equiv.swap_apply_def]
  split_ifs <;> simp_all [KroneckerDelta, Bool.toNat, eq_comm]


-- created on 2026-10-31
-- updated on 2026-11-01
