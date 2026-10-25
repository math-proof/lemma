/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic


section

open scoped CStarAlgebra InnerProduct

open scoped ComplexOrder InnerProductSpace

universe u

namespace MetaMathlibExt.Stinespring

-- N1
theorem cstarMatrix_gram_nonneg
    {n : Type*} [Fintype n]
    {B : Type*} [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (v : n → B) :
    0 ≤ CStarMatrix.ofMatrix (Matrix.of fun i j => star (v i) * v j) := by
  classical
  rcases isEmpty_or_nonempty n with h | h
  · apply le_of_eq
    apply CStarMatrix.ext
    intro i j
    simp only [CStarMatrix.zero_apply, CStarMatrix.ofMatrix_apply, Matrix.of_apply]
    exact (IsEmpty.false i).elim
  · obtain ⟨i₀⟩ := h
    let R : CStarMatrix n n B :=
      CStarMatrix.ofMatrix (Matrix.of fun k j => if k = i₀ then v j else 0)
    have hRR : star R * R = CStarMatrix.ofMatrix (Matrix.of fun i j => star (v i) * v j) := by
      apply CStarMatrix.ext
      intro i j
      simp only [CStarMatrix.mul_apply, CStarMatrix.star_apply, R,
        CStarMatrix.ofMatrix_apply, Matrix.of_apply]
      have hterm : ∀ k : n, star (if k = i₀ then v i else 0) * (if k = i₀ then v j else 0)
          = if k = i₀ then star (v i) * v j else 0 := by
        intro k
        by_cases hk : k = i₀ <;> simp [hk]
      rw [Finset.sum_congr rfl (fun k _ => hterm k)]
      rw [Finset.sum_ite_eq' _ i₀ (fun _ => star (v i) * v j)]
      simp
    rw [← hRR]
    exact star_mul_self_nonneg _

-- N2
theorem cstarMatrix_inner_sum_nonneg
    {n : Type*} [Fintype n]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : CStarMatrix n n (H →L[ℂ] H)) (hP : 0 ≤ P) (w : n → H) :
    0 ≤ ∑ i, ∑ j, ⟪w i, P i j (w j)⟫_ℂ := by
  classical
  rw [StarOrderedRing.nonneg_iff] at hP
  refine AddSubmonoid.closure_induction (fun Q hQ => ?_) ?_ (fun P Q _ _ ihP ihQ => ?_) hP
  · obtain ⟨R, rfl⟩ := hQ
    have entry : ∀ i j : n, ⟪w i, (star R * R) i j (w j)⟫_ℂ
        = ∑ k, ⟪R k i (w i), R k j (w j)⟫_ℂ := by
      intro i j
      rw [CStarMatrix.mul_apply]
      simp only [CStarMatrix.star_apply]
      rw [sum_apply Finset.univ (fun k => star (R k i) * R k j) (w j)]
      rw [inner_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_right]
    have inner_eq : ∀ k : n, (∑ i, ∑ j, ⟪R k i (w i), R k j (w j)⟫_ℂ)
        = ⟪∑ j, R k j (w j), ∑ j, R k j (w j)⟫_ℂ := by
      intro k
      rw [sum_inner]
      apply Finset.sum_congr rfl
      intro i _
      rw [inner_sum]
    have step1 : (∑ i, ∑ j, ⟪w i, (star R * R) i j (w j)⟫_ℂ)
        = ∑ i, ∑ j, ∑ k, ⟪R k i (w i), R k j (w j)⟫_ℂ :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => entry i j
    have step2 : (∑ i, ∑ j, ∑ k, ⟪R k i (w i), R k j (w j)⟫_ℂ)
        = ∑ k, ∑ i, ∑ j, ⟪R k i (w i), R k j (w j)⟫_ℂ := by
      calc _ = ∑ i, ∑ k, ∑ j, ⟪R k i (w i), R k j (w j)⟫_ℂ :=
            Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = _ := Finset.sum_comm
    calc (∑ i, ∑ j, ⟪w i, (star R * R) i j (w j)⟫_ℂ)
        = ∑ k, ⟪∑ j, R k j (w j), ∑ j, R k j (w j)⟫_ℂ := by
          rw [step1, step2]
          exact Finset.sum_congr rfl fun k _ => inner_eq k
      _ ≥ 0 := by
          apply Finset.sum_nonneg
          intro k _
          rw [RCLike.nonneg_iff]
          exact ⟨inner_self_nonneg, inner_self_im _⟩
  · simp only [CStarMatrix.zero_apply, zero_apply, inner_zero_right,
      Finset.sum_const_zero, le_refl]
  · have hsum : (∑ i, ∑ j, ⟪w i, (P + Q) i j (w j)⟫_ℂ)
        = (∑ i, ∑ j, ⟪w i, P i j (w j)⟫_ℂ) + (∑ i, ∑ j, ⟪w i, Q i j (w j)⟫_ℂ) := by
      calc (∑ i, ∑ j, ⟪w i, (P + Q) i j (w j)⟫_ℂ)
          = ∑ i, ∑ j, (⟪w i, P i j (w j)⟫_ℂ + ⟪w i, Q i j (w j)⟫_ℂ) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            rw [CStarMatrix.add_apply, add_apply, inner_add_right]
        _ = ∑ i, ((∑ j, ⟪w i, P i j (w j)⟫_ℂ) + (∑ j, ⟪w i, Q i j (w j)⟫_ℂ)) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib
        _ = _ := Finset.sum_add_distrib
    rw [hsum]
    exact add_nonneg ihP ihQ

-- N8
theorem completion_coe_eq_of_inner_eq
    {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace ℂ E]
    {u v : E} (h : ∀ w : E, ⟪w, u⟫_ℂ = ⟪w, v⟫_ℂ) :
    (u : UniformSpace.Completion E) = v := by
  have h0' : ⟪u - v, u - v⟫_ℂ = 0 := by
    rw [inner_sub_right, h (u - v), sub_self]
  have hnorm : ‖u - v‖ = 0 := by
    have hsq : ‖u - v‖ ^ 2 = 0 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ) (u - v), h0', map_zero]
    exact sq_eq_zero_iff.mp hsq
  have hco_norm : ‖(u : UniformSpace.Completion E) - v‖ = 0 := by
    rw [← UniformSpace.Completion.coe_sub, UniformSpace.Completion.norm_coe, hnorm]
  exact sub_eq_zero.mp (norm_eq_zero.mp hco_norm)

-- N3
theorem cp_gram_sum_nonneg
    {A H : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →CP (H →L[ℂ] H)) (s : Finset A) (x : A → H) :
    0 ≤ ∑ a ∈ s, ∑ b ∈ s, ⟪x a, φ (star a * b) (x b)⟫_ℂ := by
  classical
  let M : CStarMatrix ↥s ↥s A :=
    CStarMatrix.ofMatrix (Matrix.of fun i j => star (i : A) * (j : A))
  have hM : 0 ≤ M := cstarMatrix_gram_nonneg (n := ↥s) (B := A) (fun i => (i : A))
  have hP : 0 ≤ M.map φ :=
    CompletelyPositiveMap.map_cstarMatrix_nonneg φ M hM
  have hN := cstarMatrix_inner_sum_nonneg (M.map φ) hP (fun i => x (i : A))
  simp only [CStarMatrix.map_apply, M, CStarMatrix.ofMatrix_apply,
    Matrix.of_apply] at hN
  have hgoal : (∑ a ∈ s, ∑ b ∈ s, ⟪x a, φ (star a * b) (x b)⟫_ℂ)
      = ∑ i : ↥s, ∑ j : ↥s, ⟪x ↑i, φ (star ↑i * ↑j) (x ↑j)⟫_ℂ := by
    rw [← Finset.sum_coe_sort s]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_coe_sort s]
  rw [hgoal]
  exact hN

end MetaMathlibExt.Stinespring
end
