/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DiffOpSobolev.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators.Part2
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.DifferentialOperators
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SobolevEmbedding
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.FourierInversion
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SobolevDerivatives
import Def.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding.Part5
import Def.v1.Atlas.DifferentialAnalysis.code.FourierInversion.Part7
import Def.v1.Atlas.DifferentialAnalysis.code.SobolevDerivatives
import Mathlib.Algebra.MvPolynomial.Degrees
import Theorem.v1.Atlas.DifferentialAnalysis.code.DiffOpSobolev
open scoped SchwartzMap ContDiff FourierTransform
open DifferentialOperators SobolevEmbedding SobolevSpace MvPolynomial Filter Topology MeasureTheory


noncomputable section

namespace DiffOpSobolev

variable (n : ℕ)

/-- Auxiliary recursion computing the multi-index iterated partial derivative on
`SobolevSpace n m'` by processing coordinates starting at index `k`. -/
def multiIndexDerivGo {n : ℕ} (α : Fin n → ℕ)
    (k : ℕ) (m' : ℕ) (hsum : tailMultiIndexSum α k ≤ m')
    (u : SobolevSpace n m') : SobolevSpace n (m' - tailMultiIndexSum α k) :=
  if hk : k < n then
    have hαk : α ⟨k, hk⟩ ≤ m' := by
      have := tailMultiIndexSum_succ α k hk
      omega
    let v := SobolevSpace.iteratedPartialDeriv ⟨k, hk⟩ (α ⟨k, hk⟩) hαk u
    have hsum' : tailMultiIndexSum α (k + 1) ≤ m' - α ⟨k, hk⟩ := by
      have := tailMultiIndexSum_succ α k hk
      omega
    have heq : m' - α ⟨k, hk⟩ - tailMultiIndexSum α (k + 1) =
        m' - tailMultiIndexSum α k := by
      have := tailMultiIndexSum_succ α k hk
      omega
    heq ▸ multiIndexDerivGo α (k + 1) (m' - α ⟨k, hk⟩) hsum' v
  else
    have heq : tailMultiIndexSum α k = 0 := tailMultiIndexSum_ge α k (by omega)
    heq ▸ u
  termination_by n - k

/-- The monomial `x^α := ∏ x_i^{α_i}` viewed as a multivariate polynomial. -/
def multiIndexMonomial (α : Fin n → ℕ) : MvPolynomial (Fin n) ℂ :=
  MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm α) 1

end DiffOpSobolev
end
