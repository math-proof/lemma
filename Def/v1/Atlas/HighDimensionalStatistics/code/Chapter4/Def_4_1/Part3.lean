/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Def_4_1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_2
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Def_1_2
import Structure.v1.Atlas.HighDimensionalStatistics.code.Chapter4.Def_4_1.Part2
open MeasureTheory Matrix Real Finset


noncomputable section

/-- Reconstruct a matrix from its SVD data:
$\sum_j \sigma_j\, u_j v_j^\top$. -/
def SVD.toMatrix {d T : ℕ} (S : SVD d T) : Matrix (Fin d) (Fin T) ℝ :=
  ∑ j : Fin S.r, S.σval j • vecMulVec (S.u j) (S.v j)

/-- `S` is a singular value decomposition of `A` when `A` equals the matrix reconstructed
from `S`. -/
def SVD.IsDecompOf {d T : ℕ} (S : SVD d T) (A : Matrix (Fin d) (Fin T) ℝ) : Prop :=
  A = S.toMatrix

/-- Apply singular value thresholding at level `2τ` to an SVD:
$\sum_j \sigma_j \mathbf{1}(|\sigma_j| > 2\tau)\, u_j v_j^\top$. -/
def SVD.svtMatrix {d T : ℕ} (S : SVD d T) (τ : ℝ) : Matrix (Fin d) (Fin T) ℝ :=
  ∑ j : Fin S.r, (if |S.σval j| > 2 * τ then S.σval j else 0) •
    vecMulVec (S.u j) (S.v j)

/-- `Θhat` is the singular value thresholding (SVT) estimator at threshold `τ` for the
observation `y` if it arises from thresholding the singular values of some SVD of `y`. -/
def IsSVTEstimator {d T : ℕ} (y Θhat : Matrix (Fin d) (Fin T) ℝ) (τ : ℝ) : Prop :=
  ∃ S : SVD d T, S.IsDecompOf y ∧ Θhat = S.svtMatrix τ

/-- Constructive form of the singular value thresholding estimator, given an explicit SVD `S`
and threshold `τ`. -/
def singularValueThresholding {d T : ℕ} (S : SVD d T) (τ : ℝ) :
    Matrix (Fin d) (Fin T) ℝ :=
  S.svtMatrix τ

/-- **Definition 4.1** (Singular Value Thresholding estimator): `Θhat` is an SVT estimator of
threshold `τ` for the observation `y`. -/
def definition_4_1 {d T : ℕ} (y Θhat : Matrix (Fin d) (Fin T) ℝ) (τ : ℝ) : Prop :=
  IsSVTEstimator y Θhat τ

end
