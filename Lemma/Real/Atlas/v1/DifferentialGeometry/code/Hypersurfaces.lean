import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.DifferentialGeometry.code.Hypersurfaces
open Matrix Finset BigOperators in


/--
[firstFundamentalForm_eq_conjTranspose_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Hypersurfaces.lean)
-/
@[path]
lemma firstFundamentalForm_eq_conjTranspose_mul
  {n : ℕ}
  {patch : HypersurfacePatch n}
  {x : Fin n → ℝ} :
-- imply
  firstFundamentalForm patch x = (jacobianMatrix patch x)ᴴ * (jacobianMatrix patch x) := by
-- proof
  ext i j
  simp [firstFundamentalForm, jacobianMatrix, mul_apply, of_apply, dotProduct]

/--
[jacobian_mulVec_eq_fderiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Hypersurfaces.lean)
-/
@[path]
lemma jacobian_mulVec_eq_fderiv
  {n : ℕ}
  {patch : HypersurfacePatch n}
  {x v : Fin n → ℝ} :
-- imply
  jacobianMatrix patch x *ᵥ v = fderiv ℝ patch.f x v := by
-- proof
  ext k
  simp only [jacobianMatrix, mulVec, dotProduct, of_apply]
  have hv : v = ∑ i : Fin n, v i • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Finset.mem_univ]
  conv_rhs => rw [hv, map_sum]
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]

/--
[firstFundamentalForm_posDef](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Hypersurfaces.lean)
-/
@[path]
lemma firstFundamentalForm_posDef
  {n : ℕ}
  {patch : HypersurfacePatch n}
  {x : Fin n → ℝ}
-- given
  (hx : x ∈ patch.domain) :
-- imply
  (firstFundamentalForm patch x).PosDef := by
-- proof
  apply PosDef.of_dotProduct_mulVec_pos
  · rw [firstFundamentalForm_eq_conjTranspose_mul]
    exact isHermitian_conjTranspose_mul_self _
  · intro v hv
    rw [firstFundamentalForm_eq_conjTranspose_mul, ← mulVec_mulVec,
      dotProduct_mulVec, vecMul_conjTranspose, star_star]
    rw [dotProduct_star_self_pos_iff, jacobian_mulVec_eq_fderiv]
    intro h
    exact hv (patch.immersion x hx (h.trans (map_zero _).symm))

/--
[secondFundamentalForm_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Hypersurfaces.lean)
-/
@[path]
lemma secondFundamentalForm_symmetric
  {n : ℕ}
  {n : ℕ}
  {patch : HypersurfacePatch n}
  {x : Fin n → ℝ}
  {i j : Fin n}
-- given
  (hx : x ∈ patch.domain) :
-- imply
  secondFundamentalForm patch x i j = secondFundamentalForm patch x j i := by
-- proof
  simp only [secondFundamentalForm, of_apply]
  congr 1
  have hfat : ContDiffAt ℝ ⊤ patch.f x :=
    patch.smooth.contDiffAt (patch.domain_open.mem_nhds hx)
  have hfderiv_diff : DifferentiableAt ℝ (fderiv ℝ patch.f) x :=
    (hfat.fderiv_right (m := ⊤) le_top).differentiableAt (by exact WithTop.top_ne_zero)
  have hconn : ∀ (v w : Fin n → ℝ),
    fderiv ℝ (fun y => fderiv ℝ patch.f y v) x w = (fderiv ℝ (fderiv ℝ patch.f) x w) v := by
    intro v w
    have hcomp : (fun y => fderiv ℝ patch.f y v) =
      (ContinuousLinearMap.apply ℝ (Fin (n + 1) → ℝ) v) ∘ (fderiv ℝ patch.f) := by
      ext y; simp [ContinuousLinearMap.apply_apply]
    rw [hcomp, fderiv_comp x]
    · simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
    · exact (ContinuousLinearMap.apply ℝ (Fin (n + 1) → ℝ) v).differentiableAt
    · exact hfderiv_diff
  rw [hconn, hconn]
  exact (hfat.isSymmSndFDerivAt_of_omega).eq (Pi.single i 1) (Pi.single j 1)

/--
[dotProduct_sum_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Hypersurfaces.lean)
-/
@[path]
lemma dotProduct_sum_smul
  {n : ℕ}
  {m k : ℕ}
  {v : Fin k → (Fin m → ℝ)}
  {a : Fin k → ℝ}
  {w : Fin m → ℝ} :
-- imply
  (∑ j, a j • v j) ⬝ᵥ w = ∑ j, a j * (v j ⬝ᵥ w) := by
-- proof
  simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1; ext k
  rw [Finset.mul_sum]
  congr 1; ext i; ring

/--
[generalizedCross_linear_combination](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Hypersurfaces.lean)
-/
@[path]
lemma generalizedCross_linear_combination
  {n : ℕ}
  {n : ℕ}
  {v : Fin n → (Fin (n + 1) → ℝ)}
  {A : Matrix (Fin n) (Fin n) ℝ} :
-- imply
  generalizedCross (fun i => ∑ j : Fin n, A j i • v j) = A.det • generalizedCross v := by
-- proof
  ext j
  simp only [generalizedCross, Pi.smul_apply, smul_eq_mul]
  ring_nf
  congr 1
  have h : (Matrix.of (fun (i : Fin n) (k : Fin n) =>
    (∑ l : Fin n, A l i • v l) (Fin.succAbove j k))) =
    A.transpose * (Matrix.of (fun (i : Fin n) (k : Fin n) => v i (Fin.succAbove j k))) := by
    ext i k
    simp [mul_apply, transpose_apply, of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [h, det_mul, det_transpose]

/--
[gaussNormal_coordinate_change](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Hypersurfaces.lean)
-/
@[path]
lemma gaussNormal_coordinate_change
  {n : ℕ}
  {n : ℕ}
  {patch tildeP : HypersurfacePatch n}
  {φ : (Fin n → ℝ) → (Fin n → ℝ)}
  {x : Fin n → ℝ}
-- given
  (h_eq : tildeP.f = patch.f ∘ φ)
  (hφ : DifferentiableAt ℝ φ x)
  (hf : DifferentiableAt ℝ patch.f (φ x))
  (hdet_pos : (coordinateJacobian φ x).det > 0) :
-- imply
  gaussNormal tildeP x = gaussNormal patch (φ x) := by
-- proof
  have hchain : fderiv ℝ tildeP.f x = (fderiv ℝ patch.f (φ x)).comp (fderiv ℝ φ x) := by
    conv_lhs => rw [h_eq]; exact fderiv_comp x hf hφ
  have hpartials : (fun i => fderiv ℝ tildeP.f x (Pi.single i 1)) =
    (fun i => ∑ k : Fin n, (coordinateJacobian φ x) k i •
      fderiv ℝ patch.f (φ x) (Pi.single k 1)) := by
    ext i
    rw [hchain, ContinuousLinearMap.comp_apply]
    have : (fderiv ℝ φ x (Pi.single i 1) : Fin n → ℝ) =
      ∑ k : Fin n, (fderiv ℝ φ x (Pi.single i 1) k) •
        (Pi.single k (1 : ℝ) : Fin n → ℝ) := by
      ext p; simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    rw [this, map_sum]
    simp only [ContinuousLinearMap.map_smul, coordinateJacobian, of_apply]
  have hpartials2 : tildeP.partialDeriv x =
    (fun i => ∑ k : Fin n, (coordinateJacobian φ x) k i •
      patch.partialDeriv (φ x) k) := by
    unfold HypersurfacePatch.partialDeriv
    exact hpartials
  unfold gaussNormal
  rw [hpartials2, generalizedCross_linear_combination]
  ext j
  simp only [Pi.smul_apply, smul_eq_mul, dotProduct]
  have h1 : ∑ i, (coordinateJacobian φ x).det *
    (generalizedCross (patch.partialDeriv (φ x))) i *
    ((coordinateJacobian φ x).det *
    (generalizedCross (patch.partialDeriv (φ x))) i) =
    (coordinateJacobian φ x).det ^ 2 * ∑ i,
    (generalizedCross (patch.partialDeriv (φ x))) i *
    (generalizedCross (patch.partialDeriv (φ x))) i := by
    rw [Finset.mul_sum]; congr 1; ext i; ring
  rw [h1, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (le_of_lt hdet_pos)]
  field_simp

/--
[firstFundamentalForm_coordinate_change](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Hypersurfaces.lean)
-/
@[path]
lemma firstFundamentalForm_coordinate_change
  {n : ℕ}
  {n : ℕ}
  {patch tildeP : HypersurfacePatch n}
  {φ : (Fin n → ℝ) → (Fin n → ℝ)}
  {x : Fin n → ℝ}
-- given
  (h_eq : tildeP.f = patch.f ∘ φ)
  (hφ : DifferentiableAt ℝ φ x)
  (hf : DifferentiableAt ℝ patch.f (φ x)) :
-- imply
  firstFundamentalForm tildeP x = (coordinateJacobian φ x).transpose * firstFundamentalForm patch (φ x) * (coordinateJacobian φ x) := by
-- proof
  have hchain : fderiv ℝ tildeP.f x = (fderiv ℝ patch.f (φ x)).comp (fderiv ℝ φ x) := by
    conv_lhs => rw [h_eq]; exact fderiv_comp x hf hφ
  have expand : ∀ m : Fin n, fderiv ℝ tildeP.f x (Pi.single m 1) =
    ∑ k : Fin n, (fderiv ℝ φ x (Pi.single m 1) k) •
      fderiv ℝ patch.f (φ x) (Pi.single k 1) := by
    intro m
    have h1 : fderiv ℝ tildeP.f x (Pi.single m 1) =
      fderiv ℝ patch.f (φ x) (fderiv ℝ φ x (Pi.single m 1)) := by
      rw [hchain]; rfl
    rw [h1]
    have h2 : (fderiv ℝ φ x (Pi.single m 1) : Fin n → ℝ) =
      ∑ k : Fin n, (fderiv ℝ φ x (Pi.single m 1) k) •
        (Pi.single k (1 : ℝ) : Fin n → ℝ) := by
      ext p; simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    conv_lhs => rw [h2]
    rw [map_sum]
    simp only [ContinuousLinearMap.map_smul]
  ext i j
  simp only [firstFundamentalForm, of_apply, mul_apply, transpose_apply,
    coordinateJacobian, dotProduct, Finset.sum_mul]
  rw [expand i, expand j]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1; ext l
  rw [Finset.sum_comm]
  congr 1; ext k
  congr 1; ext p
  ring

/--
[secondFundamentalForm_coordinate_change_of_entries](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Hypersurfaces.lean)
-/
@[path]
lemma secondFundamentalForm_coordinate_change_of_entries
  {n : ℕ}
  {n : ℕ}
  {patch tildeP : HypersurfacePatch n}
  {φ : (Fin n → ℝ) → (Fin n → ℝ)}
  {x : Fin n → ℝ}
-- given
  (h_chain : ∀ i j : Fin n, secondFundamentalForm tildeP x i j = ∑ k, ∑ l, (coordinateJacobian φ x) k i * secondFundamentalForm patch (φ x) k l * (coordinateJacobian φ x) l j) :
-- imply
  secondFundamentalForm tildeP x = (coordinateJacobian φ x).transpose * secondFundamentalForm patch (φ x) * (coordinateJacobian φ x) := by
-- proof
  ext i j
  rw [h_chain]
  simp only [mul_apply, transpose_apply, coordinateJacobian, of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/--
[shapeOperator_coordinate_change](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Hypersurfaces.lean)
-/
@[path]
lemma shapeOperator_coordinate_change
  {n : ℕ}
  {n : ℕ}
  {patch tildeP : HypersurfacePatch n}
  {φ : (Fin n → ℝ) → (Fin n → ℝ)}
  {x : Fin n → ℝ}
-- given
  (hG : firstFundamentalForm tildeP x = (coordinateJacobian φ x).transpose * firstFundamentalForm patch (φ x) * (coordinateJacobian φ x))
  (hH : secondFundamentalForm tildeP x = (coordinateJacobian φ x).transpose * secondFundamentalForm patch (φ x) * (coordinateJacobian φ x))
  (hφ_det : IsUnit (coordinateJacobian φ x).det)
  (hG_det : IsUnit (firstFundamentalForm patch (φ x)).det) :
-- imply
  shapeOperator tildeP x = (coordinateJacobian φ x)⁻¹ * shapeOperator patch (φ x) * (coordinateJacobian φ x) := by
-- proof
  unfold shapeOperator
  rw [hG, hH]
  set Dφ := coordinateJacobian φ x
  set G := firstFundamentalForm patch (φ x)
  set H := secondFundamentalForm patch (φ x)
  have hAt : IsUnit Dφ.transpose.det := by rw [det_transpose]; exact hφ_det
  have hAtBA : IsUnit (Dφ.transpose * G * Dφ).det := by
    rw [det_mul, det_mul, det_transpose]; exact (hφ_det.mul hG_det).mul hφ_det
  have h : Dφ.transpose * G * Dφ * (Dφ⁻¹ * (G⁻¹ * H) * Dφ) = Dφ.transpose * H * Dφ := by
    have : Dφ.transpose * G * Dφ * (Dφ⁻¹ * (G⁻¹ * H) * Dφ) =
      Dφ.transpose * G * (Dφ * Dφ⁻¹) * (G⁻¹ * H) * Dφ := by
      simp only [mul_assoc]
    rw [this, mul_nonsing_inv _ hφ_det]
    simp only [mul_one, mul_assoc]
    rw [← mul_assoc G G⁻¹, mul_nonsing_inv _ hG_det, one_mul]
  have key := congr_arg ((Dφ.transpose * G * Dφ)⁻¹ * ·) h
  simp only at key
  rwa [nonsing_inv_mul_cancel_left _ _ hAtBA] at key
noncomputable section
open Matrix Finset BigOperators

/--
[firstFundamentalForm_eq_transpose_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Hypersurfaces.lean)
-/
@[path]
lemma firstFundamentalForm_eq_transpose_mul
  {n : ℕ}
  {n : ℕ}
  {patch : HypersurfacePatch n}
  {x : Fin n → ℝ} :
-- imply
  firstFundamentalForm patch x = (jacobianMatrix patch x).transpose * (jacobianMatrix patch x) := by
-- proof
  have h := firstFundamentalForm_eq_conjTranspose_mul patch x
  rwa [conjTranspose_eq_transpose_of_trivial] at h
end
noncomputable section
open Matrix Finset BigOperators

/--
[dotProduct_self_eq_one_of_sqrt_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Hypersurfaces.lean)
-/
@[path]
lemma dotProduct_self_eq_one_of_sqrt_eq_one
  {n : ℕ}
  {n : ℕ}
  {ν : Fin (n + 1) → ℝ}
-- given
  (h : Real.sqrt (ν ⬝ᵥ ν) = 1) :
-- imply
  ν ⬝ᵥ ν = 1 := by
-- proof
  have hnn : (0 : ℝ) ≤ ν ⬝ᵥ ν := by
    simp only [dotProduct]
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (ν i))
  nlinarith [Real.sq_sqrt hnn]

/--
[det_gram_eq_cross_dotProduct_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Hypersurfaces.lean)
-/
@[path]
lemma det_gram_eq_cross_dotProduct_self
  {n : ℕ}
  {v : Fin 2 → (Fin 3 → ℝ)} :
-- imply
  (Matrix.of (fun i j : Fin 2 => (v i) ⬝ᵥ (v j))).det = (generalizedCross v) ⬝ᵥ (generalizedCross v) := by
-- proof
  have hc : generalizedCross v = ![v 0 1 * v 1 2 - v 0 2 * v 1 1,
    -(v 0 0 * v 1 2 - v 0 2 * v 1 0),
    v 0 0 * v 1 1 - v 0 1 * v 1 0] := by
    ext j
    fin_cases j <;> simp [generalizedCross, det_fin_two, of_apply, Fin.succAbove,
      Fin.castSucc, Fin.succ, Fin.lt_def]
  rw [hc]
  simp [det_fin_two, of_apply, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring
end
noncomputable section
open Matrix Finset BigOperators

/--
[shapeOperatorLinkingMatrix_det](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Hypersurfaces.lean)
-/
@[path]
lemma shapeOperatorLinkingMatrix_det
  {n : ℕ}
  {n : ℕ}
  {patch : HypersurfacePatch n}
  {x : Fin n → ℝ} :
-- imply
  (shapeOperatorLinkingMatrix patch x).det = (-1 : ℝ) ^ n * (shapeOperator patch x).det := by
-- proof
  have heq : shapeOperatorLinkingMatrix patch x =
    ((Matrix.reindex finSumFinEquiv finSumFinEquiv)
      (Matrix.fromBlocks (-(shapeOperator patch x)) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℝ))) := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [shapeOperatorLinkingMatrix, of_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply]
    by_cases hin : i < n <;> by_cases hjn : j < n
    · simp only [hin, hjn, dite_true]
      show -(shapeOperator patch x) ⟨i, hin⟩ ⟨j, hjn⟩ =
        Matrix.fromBlocks (-(shapeOperator patch x)) 0 0 1
          (finSumFinEquiv.symm ⟨i, hi⟩) (finSumFinEquiv.symm ⟨j, hj⟩)
      simp [finSumFinEquiv, Fin.addCases, hin, hjn, Fin.castLT, Matrix.fromBlocks]
    · simp only [hin, hjn, dite_true, dite_false]
      show (0 : ℝ) = Matrix.fromBlocks (-(shapeOperator patch x)) 0 0 1
        (finSumFinEquiv.symm ⟨i, hi⟩) (finSumFinEquiv.symm ⟨j, hj⟩)
      simp [finSumFinEquiv, Fin.addCases, hin, hjn, Fin.castLT, Fin.subNat, Matrix.fromBlocks]
    · simp only [hin, hjn, dite_false, dite_true]
      show (0 : ℝ) = Matrix.fromBlocks (-(shapeOperator patch x)) 0 0 1
        (finSumFinEquiv.symm ⟨i, hi⟩) (finSumFinEquiv.symm ⟨j, hj⟩)
      simp [finSumFinEquiv, Fin.addCases, hin, hjn, Fin.castLT, Fin.subNat, Matrix.fromBlocks]
    · simp only [hin, hjn, dite_false]
      show (1 : ℝ) = Matrix.fromBlocks (-(shapeOperator patch x)) 0 0 1
        (finSumFinEquiv.symm ⟨i, hi⟩) (finSumFinEquiv.symm ⟨j, hj⟩)
      simp [finSumFinEquiv, Fin.addCases, hin, hjn, Fin.castLT, Fin.subNat,
        Matrix.fromBlocks, Matrix.one_apply]
      omega
  rw [heq, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg,
    Fintype.card_fin, Matrix.det_one, mul_one]
end


-- created on 2026-10-23
