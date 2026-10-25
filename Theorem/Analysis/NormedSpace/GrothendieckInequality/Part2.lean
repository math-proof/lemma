/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Def.Analysis.NormedSpace.GrothendieckInequality.Part2
open scoped InnerProductSpace


section

namespace FunctionalAnalysis.GrothendieckInequalityWanted

-- N7
theorem gtBound_mem_zero {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    (0:ℝ) ∈ { r : ℝ | ∃ d : ℕ, ∃ x : Fin m → EuclideanSpace ℝ (Fin d),
      ∃ y : Fin n → EuclideanSpace ℝ (Fin d),
      (∀ i, ‖x i‖ ≤ 1) ∧ (∀ j, ‖y j‖ ≤ 1) ∧ r = |∑ i, ∑ j, A i j * ⟪x i, y j⟫_ℝ| } := by
  refine ⟨0, fun _ => 0, fun _ => 0, fun _ => by simp, fun _ => by simp, ?_⟩
  simp

theorem gtBound_bdd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    BddAbove { r : ℝ | ∃ d : ℕ, ∃ x : Fin m → EuclideanSpace ℝ (Fin d),
      ∃ y : Fin n → EuclideanSpace ℝ (Fin d),
      (∀ i, ‖x i‖ ≤ 1) ∧ (∀ j, ‖y j‖ ≤ 1) ∧ r = |∑ i, ∑ j, A i j * ⟪x i, y j⟫_ℝ| } := by
  refine ⟨∑ i, ∑ j, |A i j|, ?_⟩
  intro r hr
  obtain ⟨d, x, y, hx, hy, rfl⟩ := hr
  calc |∑ i, ∑ j, A i j * ⟪x i, y j⟫_ℝ|
        ≤ ∑ i, |∑ j, A i j * ⟪x i, y j⟫_ℝ| :=
          Finset.abs_sum_le_sum_abs (fun i => ∑ j, A i j * ⟪x i, y j⟫_ℝ) Finset.univ
      _ ≤ ∑ i, ∑ j, |A i j * ⟪x i, y j⟫_ℝ| := by
          apply Finset.sum_le_sum
          intro i _
          exact Finset.abs_sum_le_sum_abs (fun j => A i j * ⟪x i, y j⟫_ℝ) Finset.univ
      _ ≤ ∑ i, ∑ j, |A i j| := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul]
          have hinner : |⟪x i, y j⟫_ℝ| ≤ 1 := by
            calc |⟪x i, y j⟫_ℝ| ≤ ‖x i‖ * ‖y j‖ := abs_real_inner_le_norm _ _
              _ ≤ 1 * 1 := by
                  apply mul_le_mul (hx i) (hy j) (norm_nonneg _) (by norm_num)
              _ = 1 := one_mul 1
          calc |A i j| * |⟪x i, y j⟫_ℝ| ≤ |A i j| * 1 := by
                apply mul_le_mul_of_nonneg_left hinner (abs_nonneg _)
            _ = |A i j| := mul_one _

theorem gtBound_le_of_mem {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    {r : ℝ} (hr : r ∈ { r : ℝ | ∃ d : ℕ, ∃ x : Fin m → EuclideanSpace ℝ (Fin d),
      ∃ y : Fin n → EuclideanSpace ℝ (Fin d),
      (∀ i, ‖x i‖ ≤ 1) ∧ (∀ j, ‖y j‖ ≤ 1) ∧ r = |∑ i, ∑ j, A i j * ⟪x i, y j⟫_ℝ| }) :
    r ≤ gtBound A :=
  le_csSup (gtBound_bdd A) hr

theorem gtBound_nonneg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : 0 ≤ gtBound A :=
  le_csSup (gtBound_bdd A) (gtBound_mem_zero A)

-- N8: transfer bound for arbitrary real inner product spaces
theorem abs_sum_inner_le_gtBound_mul {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (a : Fin m → E) (b : Fin n → E) (ha : ∀ i, ‖a i‖ ≤ s) (hb : ∀ j, ‖b j‖ ≤ t) :
    |∑ i, ∑ j, A i j * ⟪a i, b j⟫_ℝ| ≤ gtBound A * s * t := by
  by_cases hs0 : s = 0
  · subst hs0
    have ha0 : ∀ i, a i = 0 := fun i => norm_le_zero_iff.mp (by simpa using ha i)
    simp [ha0]
  · by_cases ht0 : t = 0
    · subst ht0
      have hb0 : ∀ j, b j = 0 := fun j => norm_le_zero_iff.mp (by simpa using hb j)
      simp [hb0]
    · have hapos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
      have hbpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      let a' : Fin m → E := fun i => s⁻¹ • a i
      let b' : Fin n → E := fun j => t⁻¹ • b j
      have ha' : ∀ i, ‖a' i‖ ≤ 1 := by
        intro i
        have e : ‖a' i‖ = s⁻¹ * ‖a i‖ := by
          simp only [a', norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hapos)]
        rw [e]
        calc s⁻¹ * ‖a i‖ ≤ s⁻¹ * s := by
              apply mul_le_mul_of_nonneg_left (ha i) (le_of_lt (inv_pos.mpr hapos))
          _ = 1 := inv_mul_cancel₀ (ne_of_gt hapos)
      have hb' : ∀ j, ‖b' j‖ ≤ 1 := by
        intro j
        have e : ‖b' j‖ = t⁻¹ * ‖b j‖ := by
          simp only [b', norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hbpos)]
        rw [e]
        calc t⁻¹ * ‖b j‖ ≤ t⁻¹ * t := by
              apply mul_le_mul_of_nonneg_left (hb j) (le_of_lt (inv_pos.mpr hbpos))
          _ = 1 := inv_mul_cancel₀ (ne_of_gt hbpos)
      obtain ⟨d, X, Y, hXn, hYn, hXY⟩ :=
        exists_euclidean_isometric_copy (m := m) (n := n) (E := E) a' b'
      have hX1 : ∀ i, ‖X i‖ ≤ 1 := fun i => by rw [hXn i]; exact ha' i
      have hY1 : ∀ j, ‖Y j‖ ≤ 1 := fun j => by rw [hYn j]; exact hb' j
      have hmem : |∑ i, ∑ j, A i j * ⟪X i, Y j⟫_ℝ| ∈
          { r : ℝ | ∃ d : ℕ, ∃ x : Fin m → EuclideanSpace ℝ (Fin d),
            ∃ y : Fin n → EuclideanSpace ℝ (Fin d),
            (∀ i, ‖x i‖ ≤ 1) ∧ (∀ j, ‖y j‖ ≤ 1) ∧
            r = |∑ i, ∑ j, A i j * ⟪x i, y j⟫_ℝ| } :=
        ⟨d, X, Y, hX1, hY1, rfl⟩
      have hle : |∑ i, ∑ j, A i j * ⟪X i, Y j⟫_ℝ| ≤ gtBound A :=
        gtBound_le_of_mem A hmem
      have eab : ∀ i j, A i j * ⟪a i, b j⟫_ℝ = (s * t) * (A i j * ⟪a' i, b' j⟫_ℝ) := by
        intro i j
        have e1 : a i = s • a' i := by
          simp only [a', ← mul_smul, mul_inv_cancel₀ (ne_of_gt hapos), one_smul]
        have e2 : b j = t • b' j := by
          simp only [b', ← mul_smul, mul_inv_cancel₀ (ne_of_gt hbpos), one_smul]
        rw [e1, e2, real_inner_smul_left, real_inner_smul_right]
        ring
      have eXY : (∑ i, ∑ j, A i j * ⟪a' i, b' j⟫_ℝ)
          = ∑ i, ∑ j, A i j * ⟪X i, Y j⟫_ℝ := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hXY i j]
      have esum : (∑ i, ∑ j, A i j * ⟪a i, b j⟫_ℝ)
          = (s * t) * (∑ i, ∑ j, A i j * ⟪X i, Y j⟫_ℝ) := by
        rw [← eXY]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        exact eab i j
      rw [esum, abs_mul]
      have hst : |s * t| = s * t := abs_of_nonneg (mul_nonneg hs ht)
      rw [hst]
      calc s * t * |∑ i, ∑ j, A i j * ⟪X i, Y j⟫_ℝ|
            ≤ s * t * gtBound A := by
              apply mul_le_mul_of_nonneg_left hle (mul_nonneg hs ht)
        _ = gtBound A * s * t := by ring

-- N9-N10 (part6)
-- N9a
theorem radEmbed_moment_a {d : ℕ} (X Y : EuclideanSpace ℝ (Fin d)) :
    ∑ ω : Fin d → Bool, radEmbed X ω * radEmbed Y ω = (2:ℝ)^d * ⟪X, Y⟫_ℝ := by
  have h := radSign_second_moment (d := d) Finset.univ (fun k => X k) (fun k => Y k)
  have eXY : (∑ k ∈ Finset.univ, X k * Y k) = ⟪X, Y⟫_ℝ := by
    simp [PiLp.inner_apply, mul_comm]
  calc ∑ ω : Fin d → Bool, radEmbed X ω * radEmbed Y ω
        = ∑ ω : Fin d → Bool, (∑ k ∈ Finset.univ, radSign k ω * X k)
          * (∑ l ∈ Finset.univ, radSign l ω * Y l) := rfl
      _ = (2:ℝ)^d * ∑ k ∈ Finset.univ, X k * Y k := h
      _ = (2:ℝ)^d * ⟪X, Y⟫_ℝ := by rw [eXY]

-- N9b
theorem radEmbed_moment_b {d : ℕ} (X : EuclideanSpace ℝ (Fin d)) :
    ∑ ω : Fin d → Bool, (radEmbed X ω)^2 = (2:ℝ)^d * ‖X‖^2 := by
  calc ∑ ω : Fin d → Bool, (radEmbed X ω)^2
        = ∑ ω : Fin d → Bool, radEmbed X ω * radEmbed X ω :=
          Finset.sum_congr rfl (fun ω _ => sq (radEmbed X ω))
      _ = (2:ℝ)^d * ⟪X, X⟫_ℝ := radEmbed_moment_a X X
      _ = (2:ℝ)^d * ‖X‖^2 := by rw [real_inner_self_eq_norm_sq]

-- N9c
theorem radEmbed_moment_c {d : ℕ} (X : EuclideanSpace ℝ (Fin d)) :
    ∑ ω : Fin d → Bool, (radEmbed X ω)^4 ≤ 3 * (2:ℝ)^d * ‖X‖^4 := by
  have h := radSign_fourth_moment_le (d := d) Finset.univ (fun k => X k)
  have erhs : (∑ k ∈ Finset.univ, X k ^ 2) = ‖X‖^2 :=
    (EuclideanSpace.real_norm_sq_eq X).symm
  calc ∑ ω : Fin d → Bool, (radEmbed X ω)^4
        = ∑ ω : Fin d → Bool, (∑ k ∈ Finset.univ, radSign k ω * X k)^4 := rfl
      _ ≤ 3 * (2:ℝ)^d * (∑ k ∈ Finset.univ, X k ^ 2)^2 := h
      _ = 3 * (2:ℝ)^d * ‖X‖^4 := by
          rw [erhs]
          ring

end FunctionalAnalysis.GrothendieckInequalityWanted
end
