/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontProducts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.WavefrontSet
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.WavefrontSet

noncomputable section

open scoped SchwartzMap FourierTransform
open MeasureTheory Set

namespace WavefrontSet

variable {n : ℕ}

/-- A point `p` of the closed unit ball is "on the sphere" if its underlying
norm equals `1`. -/
def IsOnSphere (p : ClosedBall n) : Prop := ‖p.val‖ = 1

/-- The disjoint scattering wavefront set condition that ensures the product
`u · v` of two tempered distributions is well-defined: for every point `p` of
the closed unit ball and every direction `ω` on the sphere, if `(p, ω)` lies
in the scattering wavefront set of `u`, then the antipodal direction
`(p, -ω)` must not lie in the scattering wavefront set of `v`. -/
def DisjointWFscProductCondition
    (u v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  ∀ (p ω : ClosedBall n),
    IsOnSphere ω →
    (p, ω) ∈ WFsc u →
    (p, -ω) ∉ WFsc v

/-- The disjoint scattering wavefront set condition that ensures the
convolution `u ∗ v` of two tempered distributions is well-defined: for every
direction `θ` on the sphere and every point `q` of the closed unit ball, if
`(θ, q)` lies in the scattering wavefront set of `u`, then `(-θ, q)` must not
lie in the scattering wavefront set of `v`. This is the Fourier-dual of
`DisjointWFscProductCondition`. -/
def DisjointWFscConvolutionCondition
    (u v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  ∀ (θ q : ClosedBall n),
    IsOnSphere θ →
    (θ, q) ∈ WFsc u →
    (-θ, q) ∉ WFsc v


/-- Construction of the convolution `u ∗ v` of two tempered distributions
under the disjoint scattering wavefront set condition for convolution. -/
noncomputable def convolution_welldefined_of_disjointWFsc
    (u v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hcond : DisjointWFscConvolutionCondition u v) :
    𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  convolution_exists_of_wfsc_condition u v hcond


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

/-- Construction of the product `u · v` of two tempered distributions under
the disjoint scattering wavefront set condition for products. The product is
defined by reducing to the convolution of `𝓕 u` and `𝓕 v` via the Fourier
transform. -/
noncomputable def product_welldefined_of_disjointWFsc
    (u v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hcond : DisjointWFscProductCondition u v) :
    𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  convolution_welldefined_of_disjointWFsc (𝓕 u) (𝓕 v)
    (disjointWFscProduct_implies_disjointWFscConvolution_fourier u v hcond)

/-- Packaged form of the well-definedness statement of Theorem 12.18 of
Melrose: under the appropriate disjoint scattering wavefront set conditions,
the product and convolution of two tempered distributions are simultaneously
well-defined. -/
noncomputable def welldefined_of_disjointWFsc
    (u v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    (DisjointWFscProductCondition u v → 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) ×
    (DisjointWFscConvolutionCondition u v → 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :=
  ⟨product_welldefined_of_disjointWFsc u v,
   convolution_welldefined_of_disjointWFsc u v⟩


end WavefrontSet

end
