import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Algebra.Order.Star.Real
import Lemma.Matrix.PosDefAsymm.is.PosDefAdd_T
import Lemma.Matrix.Dot_MulVecT.eq.Dot_MulVec
import Lemma.Matrix.DotVecMul_Diagonal.eq.Sum_MulMul
import sympy.matrices.dense
import sympy.core.singleton
open Matrix


@[main, comm, mp, mpr]
private lemma main
  [Fintype α] [DecidableEq α]
-- given
  (A : Matrix α α ℝ) :
-- imply
  PosDefAsymm A ↔ ∃ η : ℝ⁺, ∀ x, η * (x ⬝ᵥ x) ≤ x ⬝ᵥ (A *ᵥ x) := by
-- proof
  by_cases hα : Nonempty α
  case neg =>
    simp at hα
    constructor
    case mp =>
      intro h
      use ⟨1, by positivity⟩
      simp [dotProduct]
    case mpr =>
      intro h
      constructor
      intro x hx
      have hx0 : x = 0 := by
        funext i
        exact (IsEmpty.false i).elim
      exact (hx hx0).elim
  case pos =>
    constructor
    case mp =>
      intro hAsymm
      have h : Matrix.PosDef (A + Aᵀ) := PosDefAdd_T.of.PosDefAsymm hAsymm
      let η := (Finset.univ : Finset α).inf' (by simp) h.1.eigenvalues
      have hηmin : ∀ i, η ≤ h.1.eigenvalues i := by
        intro i
        apply Finset.inf'_le
        simp
      have hηpos : 0 < η := by
        obtain ⟨i, _, hi⟩ :=
          Finset.exists_mem_eq_inf' (s := Finset.univ) (by simp) h.1.eigenvalues
        have := Matrix.PosDef.eigenvalues_pos h i
        unfold η
        rw [hi]
        exact this
      refine ⟨⟨?η, ?hηpos⟩, ?hη⟩
      case η => exact (2⁻¹ : ℝ) * η
      case hηpos => positivity
      case hη =>
        intro x
        apply (mul_le_mul_iff_of_pos_left (a := 2) (by simp)).mp
        conv_rhs => rw [two_mul]
        nth_rw 2 [← Matrix.Dot_MulVecT.eq.Dot_MulVec]
        rw [← dotProduct_add, ← Matrix.add_mulVec, h.1.spectral_theorem]
        simp
        rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul]
        rw [Matrix.DotVecMul_Diagonal.eq.Sum_MulMul]
        simp_rw [mul_assoc]
        rw [← mul_assoc, mul_inv_cancel₀]
        set U : Matrix α α ℝ := ↑h.1.eigenvectorUnitary with hUdef
        simp
        have hstar := Matrix.UnitaryGroup.star_mul_self h.1.eigenvectorUnitary
        rw [← hUdef] at hstar
        have hunit := Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_unitaryGroup_iff'.mpr hstar)
        have hxx : x ⬝ᵥ x = x ᵥ* (U * star U) ⬝ᵥ x := by
          simp [hunit]
        rw [hxx]
        have hstarU : star U = Uᵀ := by simp [star, hUdef, Matrix.conjTranspose_eq_transpose_of_trivial]
        rw [hstarU]
        rw [← Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, dotProduct]
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i hi
        apply mul_le_mul_of_nonneg
        apply hηmin
        rfl
        positivity
        nth_rw 1 [← Matrix.transpose_transpose U]
        rw [Matrix.vecMul_transpose, ← pow_two]
        apply sq_nonneg
        simp
    case mpr =>
      intro h
      obtain ⟨⟨η, hηpos⟩, hη⟩ := h
      apply Matrix.PosDefAsymm.of.PosDefAdd_T
      apply Matrix.PosDef.of_dotProduct_mulVec_pos
      · simpa using Matrix.isHermitian_add_transpose_self A
      · intro x hx
        rw [star_trivial, Matrix.add_mulVec, dotProduct_add]
        rw [Matrix.Dot_MulVecT.eq.Dot_MulVec]
        simp
        apply LT.lt.trans_le (?_) (hη x)
        apply mul_pos hηpos
        nth_rw 1 [← star_trivial x]
        apply Matrix.dotProduct_star_self_pos_iff.mpr hx


-- created on 2026-09-19
