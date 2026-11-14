import Def.LinearAlgebra.Matrix.Permutation
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic
open Matrix


@[path]
private lemma main
  {n : ℕ}
  {x : Fin n → ℂ}
  {i j : Fin n} :
-- imply
  Finset.univ.image (x ᵥ* swapMatrix i j) = Finset.univ.image x := by
-- proof
  have vm : x ᵥ* swapMatrix i j = x ∘ Equiv.swap i j := by
    funext c
    simp only [Matrix.vecMul, dotProduct, swapMatrix, Matrix.of_apply, Function.comp_apply]
    refine (Finset.sum_eq_single (Equiv.swap i j c) (fun e _ he => ?_) (fun h => ?_)).trans ?_
    ·
      have hne : Equiv.swap i j e ≠ c := by
        intro hswap
        apply he
        rw [← hswap, Equiv.swap_apply_self]
      simp [KroneckerDelta, hne]
    ·
      apply absurd (Finset.mem_univ _) h
    ·
      simp [KroneckerDelta, Equiv.swap_apply_self]
  rw [vm, ← Finset.image_image, Finset.image_univ_equiv]


-- created on 2020-10-30
-- updated on 2026-11-13
