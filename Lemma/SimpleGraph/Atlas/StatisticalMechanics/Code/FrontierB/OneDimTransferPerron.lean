import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierB.OneDimTransferPerron
open Matrix Polynomial StatMech StatMech.FrontierB


/--
[isingTransfer_eigen_gap_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimTransferPerron.lean)
-/
@[path]
private lemma isingTransfer_eigen_gap_ne_zero_eq
-- given
  (beta h : ℝ) :
-- imply
  isingTransferEigenPlus beta h - isingTransferEigenMinus beta h ≠ 0 := by
-- proof
  apply StatMech.FrontierB.isingTransfer_eigen_gap_ne_zero beta h

/--
[isingTransferReal_charpoly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimTransferPerron.lean)
-/
@[path]
private lemma isingTransferReal_charpoly_eq
-- given
  (beta h : ℝ) :
-- imply
  (isingTransferReal beta h).charpoly = (X-C (isingTransferEigenPlus beta h))*(X-C (isingTransferEigenMinus beta h)) := by
-- proof
  apply StatMech.FrontierB.isingTransferReal_charpoly beta h

/--
[isingTransferReal_cayley_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimTransferPerron.lean)
-/
@[path]
private lemma isingTransferReal_cayley_factor_eq
-- given
  (beta h : ℝ) :
-- imply
  (isingTransferReal beta h - isingTransferEigenPlus beta h • 1) * (isingTransferReal beta h - isingTransferEigenMinus beta h • 1) = 0 := by
-- proof
  apply StatMech.FrontierB.isingTransferReal_cayley_factor beta h

/--
[isingTransfer_projectors_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimTransferPerron.lean)
-/
@[path]
private lemma isingTransfer_projectors_add_eq
-- given
  (beta h : ℝ) :
-- imply
  isingTransferProjectorPlus beta h + isingTransferProjectorMinus beta h = 1 := by
-- proof
  apply StatMech.FrontierB.isingTransfer_projectors_add beta h

/--
[isingTransfer_mul_projectorPlus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimTransferPerron.lean)
-/
@[path]
private lemma isingTransfer_mul_projectorPlus_eq
-- given
  (beta h : ℝ) :
-- imply
  isingTransferReal beta h * isingTransferProjectorPlus beta h = isingTransferEigenPlus beta h • isingTransferProjectorPlus beta h := by
-- proof
  apply StatMech.FrontierB.isingTransfer_mul_projectorPlus beta h

/--
[isingTransfer_spectral_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimTransferPerron.lean)
-/
@[path]
private lemma isingTransfer_spectral_decomposition_eq
-- given
  (beta h : ℝ) :
-- imply
  isingTransferReal beta h = isingTransferEigenPlus beta h • isingTransferProjectorPlus beta h + isingTransferEigenMinus beta h • isingTransferProjectorMinus beta h := by
-- proof
  apply StatMech.FrontierB.isingTransfer_spectral_decomposition beta h

/--
[isingTransfer_mul_projectorMinus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimTransferPerron.lean)
-/
@[path]
private lemma isingTransfer_mul_projectorMinus_eq
-- given
  (beta h : ℝ) :
-- imply
  isingTransferReal beta h * isingTransferProjectorMinus beta h = isingTransferEigenMinus beta h • isingTransferProjectorMinus beta h := by
-- proof
  apply StatMech.FrontierB.isingTransfer_mul_projectorMinus beta h

/--
[isingTransfer_pow_spectral_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimTransferPerron.lean)
-/
@[path]
private lemma isingTransfer_pow_spectral_decomposition_eq
  {n : ℕ}
-- given
  (beta h : ℝ) :
-- imply
  isingTransferReal beta h ^ n = isingTransferEigenPlus beta h ^ n • isingTransferProjectorPlus beta h + isingTransferEigenMinus beta h ^ n • isingTransferProjectorMinus beta h := by
-- proof
  apply StatMech.FrontierB.isingTransfer_pow_spectral_decomposition beta h n

/--
[isingTransfer_eigen_gap_eq_disc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimTransferPerron.lean)
-/
@[path]
private lemma isingTransfer_eigen_gap_eq_disc_eq
-- given
  (beta h : ℝ) :
-- imply
  isingTransferEigenPlus beta h - isingTransferEigenMinus beta h = isingTransferDisc beta h := by
-- proof
  apply StatMech.FrontierB.isingTransfer_eigen_gap_eq_disc beta h

/--
[isingTransfer_disc_sq_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimTransferPerron.lean)
-/
@[path]
private lemma isingTransfer_disc_sq_exp_eq
-- given
  (beta h : ℝ) :
-- imply
  isingTransferDisc beta h ^ 2 = (Real.exp (beta + h) - Real.exp (beta - h)) ^ 2 + 4 * Real.exp (-beta) ^ 2 := by
-- proof
  apply StatMech.FrontierB.isingTransfer_disc_sq_exp beta h

/--
[isingTransfer_eigenMinus_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimTransferPerron.lean)
-/
@[path]
private lemma isingTransfer_eigenMinus_exp_eq
-- given
  (beta h : ℝ) :
-- imply
  isingTransferEigenMinus beta h = (Real.exp (beta + h) + Real.exp (beta - h) - isingTransferDisc beta h) / 2 := by
-- proof
  apply StatMech.FrontierB.isingTransfer_eigenMinus_exp beta h

/--
[isingTransferProjectorPlus_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimTransferPerron.lean)
-/
@[path]
private lemma isingTransferProjectorPlus_pos_eq
  {i j : Fin 2}
-- given
  (beta h : ℝ) :
-- imply
  0 < isingTransferProjectorPlus beta h i j := by
-- proof
  apply StatMech.FrontierB.isingTransferProjectorPlus_pos beta h i j

/--
[isingTransfer_normalized_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimTransferPerron.lean)
-/
@[path]
private lemma isingTransfer_normalized_pow_eq
  {n : ℕ}
-- given
  (beta h : ℝ) :
-- imply
  (isingTransferEigenPlus beta h)⁻¹ ^ n • isingTransferReal beta h ^ n = isingTransferProjectorPlus beta h + (isingTransferEigenMinus beta h / isingTransferEigenPlus beta h) ^ n • isingTransferProjectorMinus beta h := by
-- proof
  apply StatMech.FrontierB.isingTransfer_normalized_pow beta h n

/--
[isingTransfer_normalized_pow_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimTransferPerron.lean)
-/
@[path]
private lemma isingTransfer_normalized_pow_tendsto_eq
-- given
  (beta h : ℝ) :
-- imply
  Filter.Tendsto (fun n : ℕ => (isingTransferEigenPlus beta h)⁻¹ ^ n • isingTransferReal beta h ^ n) Filter.atTop (nhds (isingTransferProjectorPlus beta h)) := by
-- proof
  apply StatMech.FrontierB.isingTransfer_normalized_pow_tendsto beta h

/--
[isingTransfer_normalized_entry_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimTransferPerron.lean)
-/
@[path]
private lemma isingTransfer_normalized_entry_tendsto_eq
  {i j : Fin 2}
-- given
  (beta h : ℝ) :
-- imply
  Filter.Tendsto (fun n : ℕ => ((isingTransferEigenPlus beta h)⁻¹ ^ n • isingTransferReal beta h ^ n) i j) Filter.atTop (nhds (isingTransferProjectorPlus beta h i j)) := by
-- proof
  apply StatMech.FrontierB.isingTransfer_normalized_entry_tendsto beta h i j

/--
[isingTransfer_entry_ratio_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimTransferPerron.lean)
-/
@[path]
private lemma isingTransfer_entry_ratio_tendsto_eq
  {i j k l : Fin 2}
-- given
  (beta h : ℝ) :
-- imply
  Filter.Tendsto (fun n : ℕ => (isingTransferReal beta h ^ n) i j / (isingTransferReal beta h ^ n) k l) Filter.atTop (nhds (isingTransferProjectorPlus beta h i j / isingTransferProjectorPlus beta h k l)) := by
-- proof
  apply StatMech.FrontierB.isingTransfer_entry_ratio_tendsto beta h i j k l

/--
[isingTransferProjectorPlus_det](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimTransferPerron.lean)
-/
@[path]
private lemma isingTransferProjectorPlus_det_eq
-- given
  (beta h : ℝ) :
-- imply
  (isingTransferProjectorPlus beta h).det = 0 := by
-- proof
  apply StatMech.FrontierB.isingTransferProjectorPlus_det beta h

/--
[isingTransferProjectorPlus_cross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimTransferPerron.lean)
-/
@[path]
private lemma isingTransferProjectorPlus_cross_eq
  {a s b : Fin 2}
-- given
  (beta h : ℝ) :
-- imply
  isingTransferProjectorPlus beta h a s * isingTransferProjectorPlus beta h s b = isingTransferProjectorPlus beta h a b * isingTransferProjectorPlus beta h s s := by
-- proof
  apply StatMech.FrontierB.isingTransferProjectorPlus_cross beta h a s b

/--
[isingTransfer_central_state_weight_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimTransferPerron.lean)
-/
@[path]
private lemma isingTransfer_central_state_weight_tendsto_eq
  {a s b : Fin 2}
-- given
  (beta h : ℝ) :
-- imply
  Filter.Tendsto (fun n : ℕ => (isingTransferReal beta h ^ n) a s * (isingTransferReal beta h ^ n) s b / (isingTransferReal beta h ^ (2 * n)) a b) Filter.atTop (nhds (isingTransferProjectorPlus beta h s s)) := by
-- proof
  apply StatMech.FrontierB.isingTransfer_central_state_weight_tendsto beta h a s b


-- created on 2026-10-23
