/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/Parametrix.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators.Part2
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.DifferentialOperators
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.CauchyKernelIntegrability
import Def.v1.Atlas.DifferentialAnalysis.code.CauchyKernelIntegrability
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated
import Theorem.v1.Atlas.DifferentialAnalysis.code.Parametrix
open scoped SchwartzMap
open MvPolynomial MeasureTheory ContinuousLinearMap Filter Asymptotics


noncomputable section

namespace DifferentialOperators

set_option maxHeartbeats 1600000 in
set_option backward.privateInPublic true in
/-- The Cauchy-Riemann tempered distribution: the action `φ ↦ ∫ φ v • cauchyRiemannKernel v`,
packaged as a tempered distribution on `ℝ²`. -/
def cauchyRiemannDistribution : 𝓢'(EuclideanSpace ℝ (Fin 2), ℂ) :=
  toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) _ _ <|
    SchwartzMap.mkCLMtoNormedSpace (𝕜 := ℂ) (E := ℂ) (G := ℂ) (σ := RingHom.id ℂ)
      (fun φ => ∫ v : EuclideanSpace ℝ (Fin 2), φ v • cauchyRiemannKernel v)
      (fun f g => by
        simp only [SchwartzMap.add_apply, add_smul]
        exact integral_add (cauchyRiemannKernel_schwartz_integrable f)
          (cauchyRiemannKernel_schwartz_integrable g))
      (fun c f => by
        simp only [SchwartzMap.smul_apply, RingHom.id_apply]
        have : (fun v : EuclideanSpace ℝ (Fin 2) => (c • f v) • cauchyRiemannKernel v) =
            (fun v => c • (f v • cauchyRiemannKernel v)) := by
          ext v; simp [smul_eq_mul, mul_assoc]
        rw [this]
        exact integral_smul c _)
      cauchyRiemannKernel_integral_bound


end DifferentialOperators
end
