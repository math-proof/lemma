/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/EigenvalueConcentration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Matrix.Spectrum
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter9.WeightedCertificates
import Lemma.Finset.Atlas.v1.ProbabilisticMethodsInCombinatorics.code.Chapter9.WeightedCertificates
open MeasureTheory Matrix Real BigOperators Finset


namespace EigenvalueConcentration

end EigenvalueConcentration

noncomputable section

namespace EigenvalueConcentration

variable {n : ℕ} [NeZero n]

/-- Number of entries on or above the diagonal of an $n \times n$ matrix: $n(n+1)/2$. -/
def numUpperTriEntries (n : ℕ) : ℕ := n * (n + 1) / 2

/-- The largest eigenvalue $\lambda_1(A)$ of a Hermitian matrix $A$, defined as the first
entry of its eigenvalue list. -/
def largestEigenvalue (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) : ℝ :=
  hA.eigenvalues₀ ⟨0, by rw [Fintype.card_fin]; exact NeZero.pos n⟩

end EigenvalueConcentration
end
