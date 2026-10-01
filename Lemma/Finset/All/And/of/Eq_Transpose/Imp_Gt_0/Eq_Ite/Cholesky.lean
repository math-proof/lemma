import sympy.matrices.cholesky
import sympy.Basic
open Matrix


@[main]
private lemma main
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) ℝ}
  {L : Matrix (Fin n) (Fin n) ℝ}
  {t : ℕ}
-- given
  (h₀ : Aᵀ = A)
  (h₁ : ∀ x : Fin n → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (A *ᵥ x))
  (h₂ : ∀ i j, L i j = if j < i then (A i j - ∑ k ∈ Finset.Iio j, L i k * L j k) / L j j else if j = i then Real.sqrt (A i i - ∑ k ∈ Finset.Iio i, ‖L i k‖ ^ 2) else 0) :
-- imply
  ∀ i : Fin n, i.val < t → 0 < L i i ∧ A i i = ∑ k ∈ Finset.Iic i, ‖L i k‖ ^ 2 ∧ ∀ j, j < i → A i j = ∑ k ∈ Finset.Iic j, L i k * L j k := by
-- proof
  have hA : A.PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ (fun x hx => ?_)
    ·
      rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, h₀]
    ·
      rw [star_trivial]
      exact h₁ x hx
  have hrec : IsCholeskyRec A L := by
    intro i j
    rw [h₂ i j]
    simp only [star_trivial, RCLike.re_to_real, RCLike.ofReal_real_eq_id, id]
  obtain ⟨hlow, hpos, hL⟩ := hA.cholesky_of_rec hrec
  have hs : ∀ i j, A i j = ∑ k ∈ Finset.Iic j, L i k * L j k := by
    intro i j
    rw [hL, Matrix.mul_conjTranspose_apply_of_lower hlow, ← Finset.Iio_insert, Finset.sum_insert (by simp), add_comm]
    simp only [star_trivial]
  intro i _hi
  refine ⟨by simpa using (RCLike.pos_iff.mp (hpos i)).1, ?_, fun j _ => hs i j⟩
  rw [hs i i]
  exact Finset.sum_congr rfl fun k _ => by rw [Real.norm_eq_abs, sq_abs, sq]


-- created on 2023-06-28
