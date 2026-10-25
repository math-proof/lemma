/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianFiniteDimensional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Instance.StatisticalMechanics.Code.SLE.BrownianFiniteDimensional.Part2
open MeasureTheory Matrix ProbabilityTheory Set WithLp
open scoped ENNReal InnerProductSpace NNReal


namespace StatMech.SLE

theorem brownianFiniteDimensionalPiLaw_isProjective :
    @IsProjectiveMeasureFamily ℝ (fun _ => ℝ) (fun _ => inferInstance)
      brownianFiniteDimensionalPiLaw := by
  intro I J hJI
  let fI : EuclideanSpace ℝ I → (I → ℝ) := @WithLp.ofLp 2 (I → ℝ)
  let fJ : EuclideanSpace ℝ J → (J → ℝ) := @WithLp.ofLp 2 (J → ℝ)
  let eRestrict : EuclideanSpace ℝ I → EuclideanSpace ℝ J :=
    EuclideanSpace.restrict₂ hJI
  let restrict : (I → ℝ) → (J → ℝ) :=
    Finset.restrict₂ (π := fun _ : ℝ => ℝ) hJI
  rw [brownianFiniteDimensionalPiLaw, brownianFiniteDimensionalPiLaw,
    ← (brownianFiniteDimensionalLaw_restrict hJI).map_eq]
  change ((brownianFiniteDimensionalLaw I).map eRestrict).map fJ =
    ((brownianFiniteDimensionalLaw I).map fI).map restrict
  have hfI : Measurable fI := WithLp.measurable_ofLp 2 (I → ℝ)
  have hfJ : Measurable fJ := WithLp.measurable_ofLp 2 (J → ℝ)
  have heRestrict : Measurable eRestrict :=
    (brownianFiniteDimensionalLaw_restrict hJI).measurable
  have hrestrict : Measurable restrict := Finset.measurable_restrict₂ hJI
  rw [Measure.map_map hfJ heRestrict, Measure.map_map hrestrict hfI]
  apply Measure.map_congr
  filter_upwards [] with x
  rfl

end StatMech.SLE
