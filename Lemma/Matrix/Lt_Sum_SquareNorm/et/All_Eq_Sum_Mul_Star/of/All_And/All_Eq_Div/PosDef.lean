import sympy.matrices.cholesky
import sympy.Basic
import Lemma.Matrix.Any_Eq_0_And_All_Gt_0_And_Eq_Mul.of.PosDef
import Lemma.Matrix.GetMul_L.eq.AddSum_Mul_Star.of.All_All_Eq_0
import Lemma.Matrix.IsCholeskyRec_Mul_L.of.All_Gt_0.All_All_Eq_0
open Matrix
open scoped ComplexOrder


/-- One step of the Cholesky induction: if rows `< t` of `L` already satisfy the Cholesky relations
and `L` satisfies the off-diagonal recursion, then row `t` satisfies the off-diagonal relations and
the diagonal radicand `A t t - ‖L[t, :t]‖²` is positive. -/
@[path]
private lemma main
  [RCLike 𝕜]
  {n : ℕ}
  {A L : Matrix (Fin n) (Fin n) 𝕜}
-- given
  (hA : A.PosDef)
  (hpiece : ∀ i j, j < i → L i j = (A i j - ∑ k ∈ Finset.Iio j, L i k * star (L j k)) / L j j)
  (t : Fin n)
  (hind : ∀ i, i < t → A i i = ((∑ k ∈ Finset.Iic i, ‖L i k‖ ^ 2 : ℝ) : 𝕜) ∧ 0 < L i i ∧ ∀ j, j < i → A i j = ∑ k ∈ Finset.Iic j, L i k * star (L j k)) :
-- imply
  ((∑ k ∈ Finset.Iio t, ‖L t k‖ ^ 2 : ℝ) : 𝕜) < A t t ∧
      ∀ j, j < t → A t j = ∑ k ∈ Finset.Iic j, L t k * star (L j k) := by
-- proof
  have hst : ∀ j, j < t → star (L j j) = L j j := fun j hj => by
    rw [RCLike.star_def, RCLike.conj_eq_iff_im]
    exact (RCLike.pos_iff.mp (hind j hj).2.1).2
  refine ⟨?_, fun j hj => ?_⟩
  ·
    obtain ⟨L₀, hlow, hpos, hL₀⟩ := Any_Eq_0_And_All_Gt_0_And_Eq_Mul.of.PosDef hA
    have h₀rec : IsCholeskyRec A L₀ := by
      rw [hL₀]
      exact IsCholeskyRec_Mul_L.of.All_Gt_0.All_All_Eq_0 hlow hpos
    have claim : ∀ j, j < t → ∀ i, j ≤ i → i ≤ t → L i j = L₀ i j := by
      intro j
      induction j using WellFoundedLT.induction with
      | _ j ih =>
        intro hjt
        have hdiag : L j j = L₀ j j := by
          have e1 : RCLike.re (A j j) = ∑ k ∈ Finset.Iio j, ‖L j k‖ ^ 2 + ‖L j j‖ ^ 2 := by
            rw [(hind j hjt).1, RCLike.ofReal_re, ← Finset.Iio_insert, Finset.sum_insert (by simp), add_comm]
          have hs : ∑ k ∈ Finset.Iio j, ‖L₀ j k‖ ^ 2 = ∑ k ∈ Finset.Iio j, ‖L j k‖ ^ 2 :=
            Finset.sum_congr rfl fun k hk => by
              rw [ih k (Finset.mem_Iio.mp hk) (lt_trans (Finset.mem_Iio.mp hk) hjt) j (le_of_lt (Finset.mem_Iio.mp hk)) hjt.le]
          rw [h₀rec j j, if_neg (lt_irrefl j), if_pos rfl, hs, e1, add_sub_cancel_left, Real.sqrt_sq (norm_nonneg _)]
          obtain ⟨x, hx, hxz⟩ := RCLike.pos_iff_exists_ofReal.mp (hind j hjt).2.1
          rw [← hxz, RCLike.norm_ofReal, abs_of_pos hx]
        intro i hji hit
        obtain hji | rfl := hji.lt_or_eq
        ·
          have hS : ∑ k ∈ Finset.Iio j, L i k * star (L j k) = ∑ k ∈ Finset.Iio j, L₀ i k * star (L₀ j k) :=
            Finset.sum_congr rfl fun k hk => by
              have hk' := Finset.mem_Iio.mp hk
              rw [ih k hk' (lt_trans hk' hjt) i (le_of_lt (lt_trans hk' hji)) hit,
                ih k hk' (lt_trans hk' hjt) j hk'.le hjt.le]
          rw [hpiece i j hji, h₀rec i j, if_pos hji, hS, hdiag]
        · exact hdiag
    have hAt : A t t = ((∑ k ∈ Finset.Iio t, ‖L t k‖ ^ 2 + ‖L₀ t t‖ ^ 2 : ℝ) : 𝕜) := by
      have hs : ∑ k ∈ Finset.Iio t, L₀ t k * star (L₀ t k) = ((∑ k ∈ Finset.Iio t, ‖L t k‖ ^ 2 : ℝ) : 𝕜) := by
        push_cast
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [← claim k (Finset.mem_Iio.mp hk) t (le_of_lt (Finset.mem_Iio.mp hk)) le_rfl, RCLike.star_def, RCLike.mul_conj]
      rw [hL₀, GetMul_L.eq.AddSum_Mul_Star.of.All_All_Eq_0 hlow, hs, RCLike.star_def, RCLike.mul_conj]
      push_cast
      ring
    rw [hAt, RCLike.ofReal_lt_ofReal]
    exact lt_add_of_pos_right _ (pow_pos (norm_pos_iff.mpr (hpos t).ne') 2)
  ·
    rw [← Finset.Iio_insert, Finset.sum_insert (by simp), hpiece t j hj, hst j hj]
    have := (hind j hj).2.1.ne'
    field_simp
    ring


-- created on 2026-10-07
