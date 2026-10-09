import sympy.matrices.cholesky
import sympy.Basic
import Lemma.Matrix.GetMul_L.eq.AddSum_Mul_Star.of.All_All_Eq_0
open Matrix
open scoped ComplexOrder


@[path]
private lemma main
  [RCLike 𝕜]
  {n : ℕ}
  {L : Matrix (Fin n) (Fin n) 𝕜}
-- given
  (hlow : ∀ i j, i < j → L i j = 0)
  (hpos : ∀ i, 0 < L i i) :
-- imply
  IsCholeskyRec (L * Lᴴ) L := by
-- proof
  have hst : ∀ j, star (L j j) = L j j := fun j => by
    rw [RCLike.star_def, RCLike.conj_eq_iff_im]
    exact (RCLike.pos_iff.mp (hpos j)).2
  intro i j
  obtain h | rfl | h := lt_trichotomy j i
  ·
    rw [if_pos h, GetMul_L.eq.AddSum_Mul_Star.of.All_All_Eq_0 hlow, hst]
    have := (hpos j).ne'
    field_simp
    ring
  ·
    rw [if_neg (lt_irrefl j), if_pos rfl, GetMul_L.eq.AddSum_Mul_Star.of.All_All_Eq_0 hlow]
    simp only [RCLike.star_def, RCLike.mul_conj, ← RCLike.ofReal_pow, ← RCLike.ofReal_sum, ← RCLike.ofReal_add,
      RCLike.ofReal_re, add_sub_cancel_left, Real.sqrt_sq (norm_nonneg _)]
    obtain ⟨x, hx, hxz⟩ := RCLike.pos_iff_exists_ofReal.mp (hpos j)
    rw [← hxz, RCLike.norm_ofReal, abs_of_pos hx]
  ·
    rw [if_neg (not_lt.mpr h.le), if_neg h.ne']
    exact hlow i j h


-- created on 2026-10-07
