/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Lemma11_5.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.Parametrix.Part2
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.Parametrix
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.CauchyKernelIntegrability
import Def.v1.Atlas.DifferentialAnalysis.code.CauchyKernelIntegrability
import Theorem.v1.Atlas.DifferentialAnalysis.code.Lemma11_5
open scoped SchwartzMap
open MvPolynomial MeasureTheory Complex Real Set Metric


noncomputable section

namespace DifferentialOperators

/-- The tempered distribution `E` defined by integration against the Cauchy–Riemann kernel
`K(z) = 1 / (2π z)`. This is the candidate fundamental solution of `∂̄` on `ℝ²`. -/
def dbarFundSolDist :
    𝓢'(EuclideanSpace ℝ (Fin 2), ℂ) :=
  SchwartzMap.mkCLMtoNormedSpace
    (fun φ => ∫ v, φ v * cauchyRiemannKernel v)
    (fun f g => by
      simp only [SchwartzMap.add_apply, add_mul]
      exact integral_add (integrable_schwartz_mul_cauchyRiemannKernel f)
        (integrable_schwartz_mul_cauchyRiemannKernel g))
    (fun c f => by
      simp only [SchwartzMap.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
      exact integral_smul c _)
    norm_integral_schwartz_cauchyRiemannKernel_le

end DifferentialOperators
end
