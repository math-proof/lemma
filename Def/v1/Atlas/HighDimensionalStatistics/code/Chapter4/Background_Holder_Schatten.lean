/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter4/Background_Holder_Schatten.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter4.Def_4_1.Part3
open Matrix Real Finset


noncomputable section

/-- The Schatten $q$-norm of a matrix given by SVD `S`:
$\|A\|_{S_q} = \bigl(\sum_j \sigma_j^q\bigr)^{1/q}$. -/
def schattenNorm {d T : ℕ} (S : SVD d T) (q : ℝ) : ℝ :=
  (∑ j : Fin S.r, S.σval j ^ q) ^ (1 / q)

/-- The nuclear norm (Schatten 1-norm) of a matrix given by SVD `S`:
the sum of its singular values. -/
def nuclearNormSVD {d T : ℕ} (S : SVD d T) : ℝ :=
  ∑ j : Fin S.r, S.σval j

/-- The Frobenius (entrywise) inner product of two matrices,
$\langle A, B\rangle_F = \sum_{i,j} A_{ij} B_{ij}$. -/
def frobeniusInnerProduct {d T : ℕ}
    (A B : Matrix (Fin d) (Fin T) ℝ) : ℝ :=
  ∑ i, ∑ j, A i j * B i j

/-- Extend the singular values of `S` (defined on `Fin S.r`) to all of `Fin (min d T)` by
zero, so that comparisons between SVDs of different ranks are easier. -/
def extendedσval {d T : ℕ} (S : SVD d T) (j : Fin (min d T)) : ℝ :=
  if h : j.val < S.r then S.σval ⟨j.val, h⟩ else 0

end
