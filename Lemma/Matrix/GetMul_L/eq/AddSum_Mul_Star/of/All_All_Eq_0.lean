import sympy.matrices.cholesky
import sympy.Basic
open Matrix
open scoped ComplexOrder


@[path]
private lemma main
  [RCLike 𝕜]
  {n : ℕ}
  {L : Matrix (Fin n) (Fin n) 𝕜}
-- given
  (hlow : ∀ i j, i < j → L i j = 0)
  (i j : Fin n) :
-- imply
  (L * Lᴴ) i j = ∑ k ∈ Finset.Iio j, L i k * star (L j k) + L i j * star (L j j) := by
-- proof
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.Iic j)) (fun k _ hk => by
      rw [hlow j k (by simpa using hk), star_zero, mul_zero]),
    ← Finset.Iio_insert, Finset.sum_insert (by simp), add_comm]


-- created on 2026-10-07
