import Def.LinearAlgebra.Matrix.Echelon.Plu
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
    simp only [Matrix.vecMul, dotProduct, swapMatrix, Matrix.of_apply, mul_ite, mul_one, mul_zero, Function.comp_apply]
    rw [Finset.sum_eq_single (Equiv.swap i j c) (fun e _ he => ite_eq_right (fun h => he (by rw [h, Equiv.swap_apply_self])))
      (fun h => absurd (Finset.mem_univ _) h), ite_eq_left (Equiv.swap_apply_self i j c).symm]
  rw [vm, ← Finset.image_image, Finset.image_univ_equiv]


-- created on 2020-10-30
