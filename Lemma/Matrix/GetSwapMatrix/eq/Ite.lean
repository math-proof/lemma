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
      if j = i₀ then (1 : α) else 0
    else if i = i₀ then
      if j = j₀ then (1 : α) else 0
    else
      if j = i then (1 : α) else 0 := by
-- proof
  simp only [swapMatrix, Matrix.of_apply]
  have hkd : (KroneckerDelta (Equiv.swap i₀ j₀ i) j : α) =
      if Equiv.swap i₀ j₀ i = j then (1 : α) else 0 := by
    simp only [KroneckerDelta]
    by_cases h : Equiv.swap i₀ j₀ i = j <;> simp [h, Bool.toNat]
  rw [hkd]
  simp only [Equiv.swap_apply_def]
  split_ifs <;> first | rfl | grind


-- created on 2026-10-31
