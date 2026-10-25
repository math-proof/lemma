/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontProducts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.DifferentialAnalysis.code.WavefrontSet.Part3
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.WavefrontSet
import Def.v1.Atlas.DifferentialAnalysis.code.WavefrontProducts


noncomputable section

open scoped SchwartzMap FourierTransform

open MeasureTheory Set

namespace WavefrontSet

variable {n : ℕ}

/-- The convolution constructed via a Schwartz / compactly-supported
decomposition of the pair `(u, v)` does not depend on the choice of
decomposition. This is the well-definedness statement underlying
Lemma 12.6 of Melrose. -/
theorem disjointWFscProduct_implies_disjointWFscConvolution_fourier
    (u v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hcond : DisjointWFscProductCondition u v) :
    DisjointWFscConvolutionCondition (𝓕 u) (𝓕 v) := by
  intro θ q hθ hθq_fu habs


  have hbnd_nq_θ : (-q, θ) ∈ BoundaryProd n := Or.inr hθ
  have h_usc : (-q, θ) ∈ WFsc u := by
    rw [mem_wfsc_iff_swap_neg_mem_wfsc_fourier u hbnd_nq_θ]
    simp only [ClosedBall.neg_neg]
    exact hθq_fu

  have hbnd_nq_nθ : (-q, -θ) ∈ BoundaryProd n := by
    right; simp [IsOnSphere] at hθ ⊢; exact hθ
  have h_vsc : (-q, -θ) ∈ WFsc v := by
    rw [mem_wfsc_iff_swap_neg_mem_wfsc_fourier v hbnd_nq_nθ]
    simp only [ClosedBall.neg_neg]
    exact habs
  exact hcond (-q) θ hθ h_usc h_vsc

end WavefrontSet
end
