/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricProduct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheScattering.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheThermodynamicReduction.Part5
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricProduct
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable def sixVertexSymmetricBetheRootAverage
    (c : ℝ) (roots : SixVertexSymmetricHalfFilledRoots) (k : ℕ) : ℝ :=
  (2 * ∑ j, Real.log ‖sixVertexBetheM c
      (sixVertexBethePhase (roots k j))‖) /
    (sixVertexFourWidth 0 k : ℝ)


def SixVertexHasSymmetricBetheIdentification
    (c : ℝ) (roots : SixVertexSymmetricHalfFilledRoots) : Prop :=
  ∀ k, sixVertexLambdaAlongFour c 0 k =
    sixVertexSymmetricBetheEigenvalueValue c (roots k)


end StatMech.FrontierD
