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
  swapMatrix (α := α) i j *ᵥ x = x ∘ Equiv.swap i j := by
-- proof
  funext k
  simp only [mulVec, dotProduct, swapMatrix, of_apply, Function.comp_apply]
  rw [Finset.sum_eq_single (Equiv.swap i j k)
    (fun e _ he => by
      have : KroneckerDelta (Equiv.swap i j k) e = 0 := by
        simp [KroneckerDelta, he.symm, Bool.toNat]
      simp [this])
    (fun h => absurd (Finset.mem_univ _) h)]
  simp [KroneckerDelta, Bool.toNat]


-- created on 2026-10-31
