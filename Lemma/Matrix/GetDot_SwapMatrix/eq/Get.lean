import Initialize.Tactic.Attr.Basic
import Def.LinearAlgebra.Matrix.Permutation
open Matrix


@[path]
private lemma main
  [Semiring α]
-- given
  (x : Fin n → α)
  (i j : Fin n) :
-- imply
  x ᵥ* swapMatrix (α := α) i j = x ∘ Equiv.swap i j := by
-- proof
  funext k
  simp only [vecMul, dotProduct, swapMatrix, of_apply, Function.comp_apply]
  rw [Finset.sum_eq_single (Equiv.swap i j k)
    (fun e _ he => by
      have : KroneckerDelta (Equiv.swap i j e) k = 0 := by
        have : Equiv.swap i j e ≠ k := by
          intro h
          apply he
          rw [← h, Equiv.swap_apply_self]
        simp [KroneckerDelta, this, Bool.toNat]
      simp [this])
    (fun h => absurd (Finset.mem_univ _) h)]
  simp [KroneckerDelta, Equiv.swap_apply_self, Bool.toNat]


-- created on 2026-10-31
