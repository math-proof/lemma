import sympy.Basic
import Mathlib.LinearAlgebra.Vandermonde
open Matrix Nat


@[path]
private lemma vandermonde
  {n : ℕ}
  {δ : ℝ} :
-- imply
  (Matrix.of fun (i j : Fin n) => ((j : ℝ) + δ) ^ (i : ℕ)).det = ∏ i : Fin n, ((i : ℕ)! : ℝ) := by
-- proof
  rw [← Matrix.det_transpose]
  have h : (Matrix.of fun (i j : Fin n) => ((j : ℝ) + δ) ^ (i : ℕ))ᵀ = Matrix.vandermonde fun j : Fin n => (j : ℝ) + δ := by
    ext i j
    simp [Matrix.vandermonde]
  have hc : ∏ x : Fin n, ∏ y ∈ Finset.Ioi x, (((y : ℕ) : ℝ) + δ - (((x : ℕ) : ℝ) + δ)) = ∏ y : Fin n, ∏ x ∈ Finset.Iio y, (((y : ℕ) : ℝ) + δ - (((x : ℕ) : ℝ) + δ)) :=
    Finset.prod_comm' (by intro x y; simp)
  rw [h, Matrix.det_vandermonde, hc]
  refine Finset.prod_congr rfl fun i _ => ?_
  have e : ∀ m : ℕ, ∏ j ∈ Finset.range m, ((m : ℝ) - j) = (m ! : ℝ) := by
    intro m
    rw [← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod, ← Finset.prod_range_reflect (fun j => ((j + 1 : ℕ) : ℝ)) m]
    refine Finset.prod_congr rfl fun j hj => ?_
    have := Finset.mem_range.mp hj
    rw [Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [← e, ← Nat.Iio_eq_range, ← Fin.map_valEmbedding_Iio, Finset.prod_map]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp


-- created on 2022-01-15
