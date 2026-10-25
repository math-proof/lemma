/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGaussianDomination.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusReflection.Part8
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}

theorem isingTorus_shiftedWeight_factor_halves
    (i : Fin d) (beta : Real)
    (u v : IsingTorusLowerSite (k := k) i → Real) :
    Real.exp (-(beta / 2) * isingTorusDirichlet
      (isingTorusEmbedLower i u + isingTorusEmbedUpper i v)) =
      isingTorusLowerHalfWeight i beta u *
        isingTorusUpperHalfWeight i beta v *
        Real.exp (beta *
          ∑ e : IsingTorusDirectedEdge d k,
            isingTorusLowerGradientFeature i u e *
              isingTorusUpperGradientFeature i v e) := by
  rw [isingTorusDirichlet_add,
    isingTorus_crossBilinear_eq_neg_featureDot]
  unfold isingTorusLowerHalfWeight isingTorusUpperHalfWeight
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem isingTorus_shiftedWeight_factor_boundary
    (i : Fin d) (beta : Real)
    (u v : IsingTorusLowerSite (k := k) i → Real) :
    Real.exp (-(beta / 2) * isingTorusDirichlet
      (isingTorusEmbedLower i u + isingTorusEmbedUpper i v)) =
      isingTorusLowerHalfWeight i beta u *
        isingTorusUpperHalfWeight i beta v *
        Real.exp (beta *
          ∑ e : IsingTorusDirectedEdge d k,
            isingTorusBoundaryFeature i u e *
              isingTorusBoundaryFeature i v e) := by
  rw [isingTorusDirichlet_add,
    isingTorus_crossBilinear_eq_neg_boundaryFeatureDot]
  unfold isingTorusLowerHalfWeight isingTorusUpperHalfWeight
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring


end StatMech.FrontierA
