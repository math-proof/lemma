import Mathlib
import sympy.Basic
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter4.Thm_4_10_Bridges
open MeasureTheory ProbabilityTheory Matrix Real Finset BigOperators Rigollet Rigollet.Chapter4 Rigollet.Chapter4.Thm_4_10_Bridges


namespace Rigollet.Chapter4.Thm_4_10_Bridges

/--
[matOpNorm_eq_matrixOpNorm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_10_Bridges.lean)
-/
@[path]
lemma matOpNorm_eq_matrixOpNorm
  {d : ℕ}
  {A : Matrix (Fin d) (Fin d) ℝ} :
-- imply
  matOpNorm A = Thm_4_6.matrixOpNorm A :=
-- proof
  rfl

end Rigollet.Chapter4.Thm_4_10_Bridges

namespace Rigollet.Chapter4.Thm_4_10_Bridges

/--
[covariance_restrict](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_10_Bridges.lean)
-/
@[path]
lemma covariance_restrict
  {d : ℕ}
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  {m n : ℕ}
  {X : Fin n → Ω → Fin d → ℝ}
  {covMat : Matrix (Fin d) (Fin d) ℝ}
  {S : Finset (Fin d)}
  {i : Fin n}
  {j k : Fin m}
-- given
  (hcard : S.card = m)
  (hcov : ∀ (i : Fin n) (j k : Fin d), ∫ ω, X i ω j * X i ω k ∂μ = covMat j k) :
-- imply
  ∫ ω, restrictSamples S hcard X i ω j * restrictSamples S hcard X i ω k ∂μ = covMat ((finsetEquivFin S) (j.cast hcard.symm)) ((finsetEquivFin S) (k.cast hcard.symm)) := by
-- proof
  simp only [restrictSamples, restrictVec]
  exact hcov i _ _

end Rigollet.Chapter4.Thm_4_10_Bridges

namespace Rigollet.Chapter4.Thm_4_10_Bridges

/--
[matOpNorm_le_of_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_10_Bridges.lean)
-/
@[path]
lemma matOpNorm_le_of_bound
  {d : ℕ}
  {k : ℕ}
  {A : Matrix (Fin k) (Fin k) ℝ}
  {M : ℝ}
-- given
  (hM : 0 ≤ M)
  (h : ∀ v : EuclideanSpace ℝ (Fin k), ‖v‖ = 1 → ‖(EuclideanSpace.equiv (Fin k) ℝ).symm (A.mulVec v)‖ ≤ M) :
-- imply
  matOpNorm A ≤ M := by
-- proof
  apply ciSup_le; intro v
  by_cases hv : ‖v‖ = 1
  · rw [ciSup_pos hv]; exact h v hv
  · rw [ciSup_neg hv, Real.sSup_empty]; exact hM

end Rigollet.Chapter4.Thm_4_10_Bridges

namespace Rigollet.Chapter4.Thm_4_10_Bridges

/--
[matOpNorm_bddAbove](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_10_Bridges.lean)
-/
@[path]
lemma matOpNorm_bddAbove
  {d : ℕ}
  {k : ℕ}
  {A : Matrix (Fin k) (Fin k) ℝ} :
-- imply
  BddAbove (Set.range (fun v : EuclideanSpace ℝ (Fin k) => ⨆ (_ : ‖v‖ = 1), ‖(EuclideanSpace.equiv (Fin k) ℝ).symm (A.mulVec v)‖)) := by
-- proof
  use ∑ i : Fin k, ∑ j : Fin k, |A i j|
  intro x hx
  simp only [Set.mem_range] at hx
  obtain ⟨v, rfl⟩ := hx
  by_cases hv : ‖v‖ = 1
  · rw [ciSup_pos hv, EuclideanSpace.norm_eq]
    have hB : (0 : ℝ) ≤ ∑ i : Fin k, ∑ j : Fin k, |A i j| :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
    rw [Real.sqrt_le_left hB]
    have hcomp : ∀ i : Fin k, ‖(A.mulVec (v : Fin k → ℝ)) i‖ ≤ ∑ j : Fin k, |A i j| := by
      intro i
      simp only [Matrix.mulVec, dotProduct]
      calc ‖∑ j, A i j * v j‖
        ≤ ∑ j, ‖A i j * v j‖ := norm_sum_le _ _
        _ ≤ ∑ j, |A i j| := by
          apply Finset.sum_le_sum; intro j _
          rw [Real.norm_eq_abs, abs_mul]
          calc |A i j| * |v j| ≤ |A i j| * 1 := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
            calc |v j| = ‖v j‖ := (Real.norm_eq_abs _).symm
              _ ≤ ‖v‖ := PiLp.norm_apply_le v j
              _ = 1 := hv
            _ = |A i j| := mul_one _
    calc ∑ i, ‖(A.mulVec (v : Fin k → ℝ)) i‖ ^ 2
      ≤ ∑ i : Fin k, (∑ j : Fin k, |A i j|) ^ 2 := by
        apply Finset.sum_le_sum; intro i _
        exact sq_le_sq' (by linarith [norm_nonneg ((A.mulVec (v : Fin k → ℝ)) i), hcomp i]) (hcomp i)
      _ ≤ (∑ i : Fin k, ∑ j : Fin k, |A i j|) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
  · rw [ciSup_neg hv, Real.sSup_empty]
    exact Finset.sum_nonneg (fun i _ =>
      Finset.sum_nonneg (fun j _ => abs_nonneg _))

end Rigollet.Chapter4.Thm_4_10_Bridges

namespace Rigollet.Chapter4.Thm_4_10_Bridges

/--
[matOpNorm_submatrix_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_10_Bridges.lean)
-/
@[path]
lemma matOpNorm_submatrix_le
  {d : ℕ}
  {m : ℕ}
  {A : Matrix (Fin d) (Fin d) ℝ}
  {S : Finset (Fin d)}
-- given
  (hcard : S.card = m) :
-- imply
  matOpNorm (d := m) (A.submatrix (fun j : Fin m => ((finsetEquivFin S) (j.cast hcard.symm)).val) (fun j : Fin m => ((finsetEquivFin S) (j.cast hcard.symm)).val)) ≤ matOpNorm A := by
-- proof
  set f : Fin m → Fin d := fun j => ((finsetEquivFin S) (j.cast hcard.symm)).val with hf_def
  have hf_inj : Function.Injective f := by
    intro a b hab
    exact Fin.ext (Fin.val_eq_of_eq (Fin.cast_injective hcard.symm
      ((finsetEquivFin S).injective (Subtype.val_injective hab))))
  apply matOpNorm_le_of_bound _ _
    (Real.iSup_nonneg (fun v => Real.iSup_nonneg (fun _ => norm_nonneg _)))
  intro vE hvE
  let v' : Fin d → ℝ := fun j' => if h : j' ∈ S then
    (vE : Fin m → ℝ) (Fin.cast hcard ((finsetEquivFin S).symm ⟨j', h⟩)) else 0
  let v'E : EuclideanSpace ℝ (Fin d) := (WithLp.equiv 2 (Fin d → ℝ)).symm v'
  have hv'_eq : ∀ j : Fin m, v' (f j) = (vE : Fin m → ℝ) j := by
    intro j; simp only [v', hf_def]
    rw [dif_pos ((finsetEquivFin S) (Fin.cast hcard.symm j)).prop]
    simp [Equiv.symm_apply_apply]
  have hv'E : ‖v'E‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    have hsum : ∑ j : Fin d,
      ‖(if h : j ∈ S then (vE : Fin m → ℝ) (Fin.cast hcard ((finsetEquivFin S).symm ⟨j, h⟩)) else 0)‖ ^ 2 =
      ∑ j : Fin m, ‖(vE : Fin m → ℝ) j‖ ^ 2 := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S)]
      have hzero : ∑ x ∈ Finset.univ.filter (fun j => j ∉ S),
        ‖(if h : x ∈ S then (vE : Fin m → ℝ) (Fin.cast hcard ((finsetEquivFin S).symm ⟨x, h⟩)) else 0)‖ ^ 2 = 0 := by
        apply Finset.sum_eq_zero; intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        simp [dif_neg hx]
      rw [hzero, add_zero]
      have hfilt : Finset.filter (· ∈ S) Finset.univ = S := by ext; simp
      rw [hfilt]
      symm
      apply Finset.sum_nbij
        (fun (x : Fin m) => ((finsetEquivFin S) (Fin.cast hcard.symm x) : Fin d))
      · intro a _; exact ((finsetEquivFin S) (Fin.cast hcard.symm a)).prop
      · intro a₁ _ a₂ _ h
        exact Fin.ext (Fin.val_eq_of_eq (Fin.cast_injective hcard.symm
          ((finsetEquivFin S).injective (Subtype.val_injective h))))
      · intro b hb
        simp only [Set.mem_image, Finset.mem_coe, Finset.mem_univ, true_and]
        obtain ⟨j, hj⟩ := (finsetEquivFin S).surjective ⟨b, hb⟩
        exact ⟨Fin.cast hcard j, by simp [hj]⟩
      · intro a _
        congr 1; simp only [dif_pos ((finsetEquivFin S) (Fin.cast hcard.symm a)).prop]
        congr 1; simp [Equiv.symm_apply_apply]
    change √(∑ i, ‖(if h : i ∈ S then (vE : Fin m → ℝ) (Fin.cast hcard ((finsetEquivFin S).symm ⟨i, h⟩)) else 0)‖ ^ 2) = 1
    rw [hsum, ← EuclideanSpace.norm_eq, hvE]
  have hmulvec : ∀ i : Fin m, (A.submatrix f f).mulVec (vE : Fin m → ℝ) i =
    (A.mulVec v') (f i) := by
    intro i
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S)]
    simp only [Finset.filter_not]
    have hzero : ∑ x ∈ Finset.univ \ Finset.filter (· ∈ S) Finset.univ,
      A (f i) x * v' x = 0 := by
      apply Finset.sum_eq_zero; intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and] at hx
      simp only [v', dif_neg hx, mul_zero]
    rw [hzero, add_zero]
    have hfilt : Finset.filter (· ∈ S) Finset.univ = S := by ext; simp
    rw [hfilt]
    apply Finset.sum_nbij
      (fun (x : Fin m) => ((finsetEquivFin S) (Fin.cast hcard.symm x) : Fin d))
    · intro a _; exact ((finsetEquivFin S) (Fin.cast hcard.symm a)).prop
    · intro a₁ _ a₂ _ h
      exact Fin.ext (Fin.val_eq_of_eq (Fin.cast_injective hcard.symm
        ((finsetEquivFin S).injective (Subtype.val_injective h))))
    · intro b hb
      simp only [Set.mem_image, Finset.mem_coe, Finset.mem_univ, true_and]
      obtain ⟨j, hj⟩ := (finsetEquivFin S).surjective ⟨b, hb⟩
      exact ⟨Fin.cast hcard j, by simp [hj]⟩
    · intro a _; congr 1; exact (hv'_eq a).symm
  have hnorm_le : ‖(EuclideanSpace.equiv (Fin m) ℝ).symm ((A.submatrix f f).mulVec vE)‖ ≤
    ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec v'E)‖ := by
    simp only [EuclideanSpace.norm_eq]
    apply Real.sqrt_le_sqrt
    calc ∑ i : Fin m, ‖((A.submatrix f f).mulVec (vE : Fin m → ℝ)) i‖ ^ 2
      = ∑ i : Fin m, ‖(A.mulVec v') (f i)‖ ^ 2 := by
        congr 1; ext i; rw [hmulvec]
      _ = ∑ j ∈ Finset.univ.image f, ‖(A.mulVec v') j‖ ^ 2 := by
        rw [Finset.sum_image (fun a _ b _ h => hf_inj h)]
      _ ≤ ∑ j : Fin d, ‖(A.mulVec v') j‖ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · exact fun x _ => Finset.mem_univ x
        · intro i _ _; positivity
  calc ‖(EuclideanSpace.equiv (Fin m) ℝ).symm ((A.submatrix f f).mulVec vE)‖
    ≤ ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec v'E)‖ := hnorm_le
    _ ≤ ⨆ (_ : ‖v'E‖ = 1), ‖(EuclideanSpace.equiv (Fin d) ℝ).symm (A.mulVec v'E)‖ := by
      rw [ciSup_pos hv'E]
    _ ≤ matOpNorm A := le_ciSup (matOpNorm_bddAbove A) v'E

end Rigollet.Chapter4.Thm_4_10_Bridges

namespace Rigollet.Chapter4.Thm_4_10_Bridges

/--
[whitening_reduction_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_10_Bridges.lean)
-/
@[path]
lemma whitening_reduction_bridge
  {d : ℕ}
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {n : ℕ}
  {X : Fin n → Ω → Fin d → ℝ}
  {covMat : Matrix (Fin d) (Fin d) ℝ}
  {t : ℝ}
-- given
  (hn : 0 < n)
  (hd : 0 < d)
  (hcov : ∀ (i : Fin n) (j k : Fin d), ∫ ω, X i ω j * X i ω k ∂μ = covMat j k)
  (hSubG : ∀ (i : Fin n), Thm_4_6.IsSubGaussianVec μ (X i) (matOpNorm covMat))
  (hIndepFun : iIndepFun (m := fun _ => inferInstance) X μ)
  (hPD : covMat.PosDef)
  (ht : 0 < t) :
-- imply
  μ {ω : Ω | matOpNorm (Thm_4_6.empiricalCovariance X ω - covMat) > matOpNorm covMat * t} ≤ ENNReal.ofReal ((288 : ℝ) ^ d * Real.exp (-(↑n / 2 * min ((t / 32) ^ 2) (t / 32)))) := by
-- proof
  have hSubG' : ∀ (i : Fin n),
    Thm_4_6.IsSubGaussianVec μ (X i) (Thm_4_6.matrixOpNorm covMat) := by
    intro i
    rw [← matOpNorm_eq_matrixOpNorm]
    exact hSubG i
  have hset_eq : {ω : Ω | matOpNorm (Thm_4_6.empiricalCovariance X ω - covMat) >
    matOpNorm covMat * t} =
    {ω : Ω | Thm_4_6.matrixOpNorm (Thm_4_6.empiricalCovariance X ω - covMat) >
      Thm_4_6.matrixOpNorm covMat * t} := by
    ext ω
    simp only [Set.mem_setOf_eq, matOpNorm_eq_matrixOpNorm]
  rw [hset_eq]
  exact Thm_4_6.whitening_reduction μ n hn hd X covMat hcov hSubG' hIndepFun hPD t ht

end Rigollet.Chapter4.Thm_4_10_Bridges

namespace Rigollet.Chapter4.Thm_4_10_Bridges

/--
[whitening_reduction_subproblem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Thm_4_10_Bridges.lean)
-/
@[path]
lemma whitening_reduction_subproblem
  {d : ℕ}
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {m : ℕ}
  {n : ℕ}
  {Y : Fin n → Ω → Fin m → ℝ}
  {covMatSub : Matrix (Fin m) (Fin m) ℝ}
  {t : ℝ}
-- given
  (hn : 0 < n)
  (hm : 0 < m)
  (hcov : ∀ (i : Fin n) (j k : Fin m), ∫ ω, Y i ω j * Y i ω k ∂μ = covMatSub j k)
  (hSubG : ∀ (i : Fin n), Thm_4_6.IsSubGaussianVec (d := m) μ (Y i) (matOpNorm covMatSub))
  (hIndepFun : iIndepFun (m := fun _ => inferInstance) Y μ)
  (hPD : covMatSub.PosDef)
  (ht : 0 < t) :
-- imply
  μ {ω : Ω | matOpNorm (d := m) (Thm_4_6.empiricalCovariance (d := m) Y ω - covMatSub) > matOpNorm (d := m) covMatSub * t} ≤ ENNReal.ofReal ((288 : ℝ) ^ m * Real.exp (-(↑n / 2 * min ((t / 32) ^ 2) (t / 32)))) :=
-- proof
  whitening_reduction_bridge μ n hn hm Y covMatSub hcov hSubG hIndepFun hPD t ht

end Rigollet.Chapter4.Thm_4_10_Bridges


-- created on 2026-10-23
