/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/WavefrontProducts.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.DifferentialAnalysis.code.WavefrontSet.Part3
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.WavefrontSet
import Theorem.v1.Atlas.DifferentialAnalysis.code.WavefrontProducts


noncomputable section

open scoped SchwartzMap FourierTransform

open MeasureTheory Set

namespace WavefrontSet

variable {n : ℕ}

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
