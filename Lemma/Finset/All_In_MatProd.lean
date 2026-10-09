import sympy.matrices.plu
import sympy.sets.sets
import sympy.Basic
open Matrix


@[path]
private lemma permutation
  {n m : ℕ}
  {a d : ℕ → Fin n} :
-- imply
  ∀ x ∈ {x : Fin n → ℂ | Finset.univ.image x = (Finset.range n).image (fun k : ℕ => (k : ℂ))},
    x ᵥ* ((List.range m).map fun i => swapMatrix (a i) (d i)).prod ∈ {x : Fin n → ℂ | Finset.univ.image x = (Finset.range n).image (fun k : ℕ => (k : ℂ))} := by
-- proof
  have vm : ∀ (y : Fin n → ℂ) (i j : Fin n), y ᵥ* swapMatrix i j = y ∘ Equiv.swap i j := by
    intro y i j
    funext c
    simp only [Matrix.vecMul, dotProduct, swapMatrix, Matrix.of_apply, mul_ite, mul_one, mul_zero, Function.comp_apply]
    rw [Finset.sum_eq_single (Equiv.swap i j c) (fun e _ he => if_neg (fun h => he (by rw [h, Equiv.swap_apply_self])))
      (fun h => absurd (Finset.mem_univ _) h), if_pos (Equiv.swap_apply_self i j c).symm]
  intro x hx
  induction m with
  | zero =>
    simpa using hx
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ← Matrix.vecMul_vecMul, List.map_singleton,
      List.prod_singleton, vm]
    simp only [Set.mem_ofPred_eq] at ih ⊢
    rw [← Finset.image_image, Finset.image_univ_equiv, ih]


-- created on 2020-11-02
