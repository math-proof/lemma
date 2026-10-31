import Initialize.Tactic.Attr.Basic
import Def.LinearAlgebra.Matrix.Permutation
import Mathlib.Algebra.Ring.Defs
open Matrix


@[path]
private lemma main
  [AddMonoidWithOne α]
-- given
  (i j : Fin n) :
-- imply
  (swapMatrix (α := α) i j)ᵀ = swapMatrix (α := α) i j := by
-- proof
  ext a b
  simp only [swapMatrix, transpose_apply, of_apply, KroneckerDelta]
  have hiff : Equiv.swap i j b = a ↔ Equiv.swap i j a = b := by
    constructor
    ·
      intro h
      rw [← h, Equiv.swap_apply_self]
    ·
      intro h
      rw [← h, Equiv.swap_apply_self]
  if h : Equiv.swap i j a = b then
    have h2 : Equiv.swap i j b = a := by
      apply hiff.mpr
      apply h
    simp [h, h2, Bool.toNat]
  else
    have h2 : Equiv.swap i j b ≠ a := by
      intro hb
      apply h
      apply hiff.mp
      apply hb
    simp [h, h2, Bool.toNat]


-- created on 2026-10-31
