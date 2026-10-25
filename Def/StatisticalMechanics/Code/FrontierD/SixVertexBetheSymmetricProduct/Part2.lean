/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricProduct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheScattering.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheThermodynamicReduction.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricProduct
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable def sixVertexSymmetricBetheEigenvalueCandidate
    {k : ℕ} (c : ℝ) (p : Fin k → ℝ) : ℂ :=
  (∏ j, sixVertexBetheL c (sixVertexBethePhase (p j)) *
      sixVertexBetheL c (sixVertexBethePhase (-p j))) +
    ∏ j, sixVertexBetheM c (sixVertexBethePhase (p j)) *
      sixVertexBetheM c (sixVertexBethePhase (-p j))


noncomputable def sixVertexSymmetricBetheEigenvalueValue
    {k : ℕ} (c : ℝ) (p : Fin k → ℝ) : ℝ :=
  2 * ∏ j, ‖sixVertexBetheM c (sixVertexBethePhase (p j))‖ ^ 2


end StatMech.FrontierD
