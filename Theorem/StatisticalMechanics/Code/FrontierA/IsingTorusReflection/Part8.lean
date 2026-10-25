/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGaussianDomination.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusReflection.Part7
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}

theorem isingTorus_lowerFeature_mul_upperFeature_eq_boundary
    (i : Fin d) (u v : IsingTorusLowerSite (k := k) i → Real)
    (e : IsingTorusDirectedEdge d k) :
    isingTorusLowerGradientFeature i u e *
        isingTorusUpperGradientFeature i v e =
      isingTorusBoundaryFeature i u e *
        isingTorusBoundaryFeature i v e := by
  rcases e with ⟨x, j⟩
  let y := x + isingTorusStep j
  by_cases hx : isingTorusInLowerHalf i x <;>
    by_cases hy : isingTorusInLowerHalf i y
  · simp [isingTorusBoundaryFeature, isingTorusLowerGradientFeature,
      isingTorusUpperGradientFeature, isingTorusEmbedLower,
      isingTorusEmbedUpper, y, hx, hy]
  · have href : isingTorusReflectSite i y = x :=
      (isingTorus_crossing_reflects_endpoints i j x).1 ⟨hx, hy⟩
    simp [isingTorusBoundaryFeature, isingTorusLowerGradientFeature,
      isingTorusUpperGradientFeature, isingTorusEmbedLower,
      isingTorusEmbedUpper, y, hx, hy, href]
  · have href : isingTorusReflectSite i x = y :=
      (isingTorus_crossing_reflects_endpoints i j x).2 ⟨hx, hy⟩
    simp [isingTorusBoundaryFeature, isingTorusLowerGradientFeature,
      isingTorusUpperGradientFeature, isingTorusEmbedLower,
      isingTorusEmbedUpper, y, hx, hy, href]
  · simp [isingTorusBoundaryFeature, isingTorusLowerGradientFeature,
      isingTorusUpperGradientFeature, isingTorusEmbedLower,
      isingTorusEmbedUpper, y, hx, hy]

theorem isingTorus_crossBilinear_eq_neg_boundaryFeatureDot
    (i : Fin d)
    (u v : IsingTorusLowerSite (k := k) i → Real) :
    isingTorusDirichletBilinear
        (isingTorusEmbedLower i u) (isingTorusEmbedUpper i v) =
      -(∑ e : IsingTorusDirectedEdge d k,
        isingTorusBoundaryFeature i u e *
          isingTorusBoundaryFeature i v e) := by
  unfold isingTorusDirichletBilinear
  rw [Fintype.sum_prod_type, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [← isingTorus_lowerFeature_mul_upperFeature_eq_boundary
    i u v (x, j)]
  unfold isingTorusLowerGradientFeature isingTorusUpperGradientFeature
  ring

theorem isingTorus_crossBilinear_eq_neg_featureDot
    (i : Fin d)
    (u v : IsingTorusLowerSite (k := k) i → Real) :
    isingTorusDirichletBilinear
        (isingTorusEmbedLower i u) (isingTorusEmbedUpper i v) =
      -(∑ e : IsingTorusDirectedEdge d k,
        isingTorusLowerGradientFeature i u e *
          isingTorusUpperGradientFeature i v e) := by
  unfold isingTorusDirichletBilinear
    isingTorusLowerGradientFeature isingTorusUpperGradientFeature
  rw [Fintype.sum_prod_type]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

end StatMech.FrontierA
