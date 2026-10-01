import sympy.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Fintype.Fin
open Matrix


@[main]
private lemma main
  [CommRing R]
  {n a b : ℕ}
  {M : Matrix (Fin n) (Fin n) R}
-- given
  (h₀ : a + b > n)
  (h₁ : a ≤ n)
  (h₂ : b ≤ n)
  (h₃ : ∀ i j : Fin n, (i : ℕ) < a → (j : ℕ) < b → M i j = 0) :
-- imply
  M.det = 0 := by
-- proof
  rw [Matrix.det_apply]
  refine Finset.sum_eq_zero fun σ _ => ?_
  obtain ⟨j, hj, hσ⟩ : ∃ j : Fin n, (j : ℕ) < b ∧ ((σ j : Fin n) : ℕ) < a := by
    by_contra hne
    simp only [not_exists, not_and, not_lt] at hne
    have hd : Disjoint ((Finset.univ.filter fun j : Fin n => (j : ℕ) < b).image σ) (Finset.univ.filter fun j : Fin n => (j : ℕ) < a) := by
      refine Finset.disjoint_left.mpr fun x hx hxu => ?_
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hxu
      exact absurd (hne j hj) (not_le.mpr hxu)
    have hu := Finset.card_union_add_card_inter ((Finset.univ.filter fun j : Fin n => (j : ℕ) < b).image σ) (Finset.univ.filter fun j : Fin n => (j : ℕ) < a)
    rw [Finset.disjoint_iff_inter_eq_empty.mp hd, Finset.card_empty, add_zero, Finset.card_image_of_injective _ σ.injective, Fin.card_filter_val_lt, Fin.card_filter_val_lt] at hu
    have hle := Finset.card_le_univ ((Finset.univ.filter fun j : Fin n => (j : ℕ) < b).image σ ∪ Finset.univ.filter fun j : Fin n => (j : ℕ) < a)
    rw [Fintype.card_fin] at hle
    omega
  rw [Finset.prod_eq_zero (f := fun i => M (σ i) i) (Finset.mem_univ j) (h₃ (σ j) j hσ hj), smul_zero]


-- created on 2020-10-14
