import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.DifferentialGeometry.code.GaussMapDegree.Part4
open GaussMapDegree
open scoped Matrix


namespace GaussMapDegree

/--
[det_augmented_eq_det_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/GaussMapDegree.lean)
-/
@[path]
lemma det_augmented_eq_det_mul
  {n : ℕ}
  {H : Matrix (Fin n) (Fin n) ℝ}
  {A : Matrix (Fin (n + 1)) (Fin n) ℝ}
  {ν : Fin (n + 1) → ℝ} :
-- imply
  (augmentedMatrix (A * H) ν).det = H.det * (augmentedMatrix A ν).det := by
-- proof
  set T : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.of fun i j =>
    if hi : (i : ℕ) < n then
      if hj : (j : ℕ) < n then H ⟨i, hi⟩ ⟨j, hj⟩
      else 0
    else
      if (j : ℕ) < n then 0 else 1
  suffices factored : augmentedMatrix (A * H) ν = augmentedMatrix A ν * T by
    rw [factored, Matrix.det_mul]
    suffices hT : T.det = H.det by rw [hT, mul_comm]
    rw [Matrix.det_succ_column T (Fin.last n)]
    have hcol : ∀ i : Fin (n + 1), i ≠ Fin.last n →
      T i (Fin.last n) = 0 := by
      intro i hi
      simp only [T, Matrix.of_apply]
      have hi' : (i : ℕ) < n := by
        have := i.isLt; simp [Fin.ext_iff, Fin.val_last] at hi; omega
      simp [hi']
    have hTlast : T (Fin.last n) (Fin.last n) = 1 := by
      simp [T, Matrix.of_apply]
    rw [Finset.sum_eq_single (Fin.last n)]
    · simp only [Fin.val_last, hTlast]
      have : (-1 : ℝ) ^ (n + n) = 1 := by
        have : Even (n + n) := ⟨n, by ring⟩
        exact Even.neg_one_pow this
      simp only [this, one_mul, mul_one]
      congr 1
      ext a b
      simp [Matrix.submatrix, T, Matrix.of_apply, Fin.succAbove]
    · intro i _ hi
      simp [hcol i hi]
    · intro h
      exact absurd (Finset.mem_univ _) h
  ext i j
  simp only [augmentedMatrix, Matrix.of_apply, Matrix.mul_apply, T]
  split_ifs with hj
  ·
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.lt_irrefl,
      dite_false, mul_zero, add_zero]
    congr 1
    ext k
    have hk : (k : ℕ) < n := k.isLt
    simp only [dif_pos hk]
  ·
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, Nat.lt_irrefl,
      dite_false, mul_one]
    convert (zero_add (ν i)).symm using 1
    congr 1
    apply Finset.sum_eq_zero
    intro k _
    simp

end GaussMapDegree

namespace GaussMapDegree

/--
[det_jacobian_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/GaussMapDegree.lean)
-/
@[path]
lemma det_jacobian_formula
  {n : ℕ}
  {Df : Matrix (Fin (n + 1)) (Fin n) ℝ}
  {Dφf : Matrix (Fin (n + 1)) (Fin n) ℝ}
  {ν_tilde : Fin (n + 1) → ℝ}
  {H : Matrix (Fin n) (Fin n) ℝ}
-- given
  (hchain : Df * H = Dφf)
  (hG_pos : 0 < (augmentedMatrix Df ν_tilde).det)
  (hG_sq : (augmentedMatrix Df ν_tilde).det ^ 2 = (Dfᵀ * Df).det) :
-- imply
  H.det = (augmentedMatrix Dφf ν_tilde).det / Real.sqrt ((Dfᵀ * Df).det) := by
-- proof
  have hdet_aug := det_augmented_eq_det_mul H Df ν_tilde
  rw [hchain] at hdet_aug
  have hG_ne_zero : (augmentedMatrix Df ν_tilde).det ≠ 0 := ne_of_gt hG_pos
  have hG_nonneg : (0 : ℝ) ≤ (augmentedMatrix Df ν_tilde).det := le_of_lt hG_pos
  have hG_eq_sqrt : (augmentedMatrix Df ν_tilde).det = Real.sqrt ((Dfᵀ * Df).det) := by
    rw [← hG_sq, Real.sqrt_sq hG_nonneg]
  rw [hdet_aug, hG_eq_sqrt, mul_div_cancel_right₀ _ (ne_of_gt (by rwa [← hG_eq_sqrt]))]

end GaussMapDegree

namespace GaussMapDegree

/--
[SmoothHypersurfaceMap.chain_rule_matrices](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/GaussMapDegree.lean)
-/
@[path]
lemma SmoothHypersurfaceMap.chain_rule_matrices
  {n : ℕ}
  {Φ : SmoothHypersurfaceMap n}
  {u : Fin n → ℝ}
-- given
  (hu : u ∈ Φ.domainU) :
-- imply
  Φ.sourceJacobian u * Φ.jacobianMatrix u = Φ.composedJacobian u :=
-- proof
  Φ.chain_rule u hu

end GaussMapDegree

namespace GaussMapDegree

/--
[det_augmented_sq_of_orthonormal_last_col](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/GaussMapDegree.lean)
-/
@[path]
lemma det_augmented_sq_of_orthonormal_last_col
  {n : ℕ}
  {A : Matrix (Fin (n + 1)) (Fin n) ℝ}
  {ν : Fin (n + 1) → ℝ}
-- given
  (horth : ∀ j : Fin n, ∑ i : Fin (n + 1), A i j * ν i = 0)
  (hnorm : ∑ i : Fin (n + 1), ν i ^ 2 = 1) :
-- imply
  (augmentedMatrix A ν).det ^ 2 = (Aᵀ * A).det := by
-- proof
  have h1 : (augmentedMatrix A ν).det ^ 2 =
    ((augmentedMatrix A ν)ᵀ * (augmentedMatrix A ν)).det := by
    rw [Matrix.det_mul, Matrix.det_transpose]
    ring
  rw [h1]
  set M := augmentedMatrix A ν
  set P := Mᵀ * M
  have hdet_sub : P.det =
    (P.submatrix finSumFinEquiv finSumFinEquiv).det :=
    (Matrix.det_submatrix_equiv_self finSumFinEquiv P).symm
  rw [hdet_sub]
  have hblock : P.submatrix finSumFinEquiv finSumFinEquiv =
    Matrix.fromBlocks (Aᵀ * A) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext (i | i) (j | j)
    ·
      simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁,
        P, M, Matrix.mul_apply, Matrix.transpose_apply, augmentedMatrix, Matrix.of_apply]
      simp only [finSumFinEquiv_apply_left, Fin.val_castAdd]
      have hi' : (i : ℕ) < n := i.isLt
      have hj' : (j : ℕ) < n := j.isLt
      simp only [hi', hj', dite_true]
    ·
      simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₂,
        Matrix.zero_apply, P, M, Matrix.mul_apply, Matrix.transpose_apply,
        augmentedMatrix, Matrix.of_apply]
      simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        Fin.val_castAdd, Fin.val_natAdd]
      have hi' : (i : ℕ) < n := i.isLt
      have hj_not : ¬((n + (j : ℕ)) < n) := by omega
      simp only [hi', dite_true, hj_not, dite_false]
      exact horth i
    ·
      simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₁,
        Matrix.zero_apply, P, M, Matrix.mul_apply, Matrix.transpose_apply,
        augmentedMatrix, Matrix.of_apply]
      simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        Fin.val_castAdd, Fin.val_natAdd]
      have hi_not : ¬((n + (i : ℕ)) < n) := by omega
      have hj' : (j : ℕ) < n := j.isLt
      simp only [hi_not, dite_false, hj', dite_true]
      have := horth j
      rw [show (∑ x, ν x * A x ⟨↑j, hj'⟩) = ∑ i, A i j * ν i from
        Finset.sum_congr rfl (fun k _ => by ring)]
      exact this
    ·
      simp only [Matrix.submatrix_apply, Matrix.fromBlocks_apply₂₂,
        P, M, Matrix.mul_apply, Matrix.transpose_apply, augmentedMatrix, Matrix.of_apply]
      simp only [finSumFinEquiv_apply_right, Fin.val_natAdd]
      have hi_not : ¬((n + (i : ℕ)) < n) := by omega
      have hj_not : ¬((n + (j : ℕ)) < n) := by omega
      simp only [hi_not, hj_not, dite_false]
      simp only [Matrix.one_apply]
      have hij : i = j := Subsingleton.elim i j
      simp only [hij, if_true]
      rw [show (∑ x, ν x * ν x) = ∑ i, ν i ^ 2 from
        Finset.sum_congr rfl (fun k _ => by ring)]
      exact hnorm
  rw [hblock, Matrix.det_fromBlocks_zero₂₁]
  simp

end GaussMapDegree

namespace GaussMapDegree

/--
[det_jacobian_formula_geometric](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/GaussMapDegree.lean)
-/
@[path]
lemma det_jacobian_formula_geometric
  {n : ℕ}
  {Φ : SmoothHypersurfaceMap n}
  {u : Fin n → ℝ}
  {ν_tilde : Fin (n + 1) → ℝ}
-- given
  (horth : ∀ j : Fin n, ∑ i : Fin (n + 1), (Φ.sourceJacobian u) i j * ν_tilde i = 0)
  (hnorm : ∑ i : Fin (n + 1), ν_tilde i ^ 2 = 1)
  (hpos : 0 < (augmentedMatrix (Φ.sourceJacobian u) ν_tilde).det)
  (hchain : (Φ.sourceJacobian u) * (Φ.jacobianMatrix u) = Φ.composedJacobian u) :
-- imply
  Φ.jacobianDet u = (augmentedMatrix (Φ.composedJacobian u) ν_tilde).det / Real.sqrt ((gramMatrix n Φ.σ u).det) := by
-- proof
  have hGram : gramMatrix n Φ.σ u = (Φ.sourceJacobian u)ᵀ * (Φ.sourceJacobian u) := by
    ext i j
    simp only [gramMatrix, SmoothHypersurfaceMap.sourceJacobian, Matrix.transpose_apply,
      Matrix.mul_apply]
  rw [hGram]
  have hG_sq : (augmentedMatrix (Φ.sourceJacobian u) ν_tilde).det ^ 2 =
    ((Φ.sourceJacobian u)ᵀ * (Φ.sourceJacobian u)).det :=
    det_augmented_sq_of_orthonormal_last_col (Φ.sourceJacobian u) ν_tilde horth hnorm
  exact det_jacobian_formula (Φ.sourceJacobian u) (Φ.composedJacobian u)
    ν_tilde (Φ.jacobianMatrix u) hchain hpos hG_sq

end GaussMapDegree

namespace GaussMapDegree

/--
[det_jacobian_formula_geometric_target](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/GaussMapDegree.lean)
-/
@[path]
lemma det_jacobian_formula_geometric_target
  {n : ℕ}
  {Φ : SmoothHypersurfaceMap n}
  {u : Fin n → ℝ}
-- given
  (htarget_orth_source : ∀ j : Fin n, ∑ i : Fin (n + 1), (Φ.sourceJacobian u) i j * (Φ.ν_tilde (Φ.h u)) i = 0)
  (hpos : 0 < (augmentedMatrix (Φ.sourceJacobian u) (Φ.ν_tilde (Φ.h u))).det)
  (hu : u ∈ Φ.domainU) :
-- imply
  Φ.jacobianDet u = (augmentedMatrix (Φ.composedJacobian u) (Φ.ν_tilde (Φ.h u))).det / Real.sqrt ((gramMatrix n Φ.σ u).det) := by
-- proof
  have hchain : (Φ.sourceJacobian u) * (Φ.jacobianMatrix u) =
    Φ.composedJacobian u := Φ.chain_rule_matrices u hu
  have hnorm : ∑ i : Fin (n + 1), (Φ.ν_tilde (Φ.h u)) i ^ 2 = 1 :=
    Φ.ν_tilde_norm (Φ.h u) (Φ.h_maps u hu)
  exact det_jacobian_formula_geometric Φ u (Φ.ν_tilde (Φ.h u))
    htarget_orth_source hnorm hpos hchain

end GaussMapDegree


-- created on 2026-10-23
