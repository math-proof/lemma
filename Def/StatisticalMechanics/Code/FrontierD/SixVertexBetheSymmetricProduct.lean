/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricProduct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheScattering.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheThermodynamicReduction.Part5
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable def sixVertexBethePhase (p : ℝ) : ℂ :=
  Complex.exp (Complex.I * p)


noncomputable def sixVertexBetheL (c : ℝ) (z : ℂ) : ℂ :=
  1 + (c : ℂ) ^ 2 * z / (1 - z)


noncomputable def sixVertexBetheM (c : ℝ) (z : ℂ) : ℂ :=
  1 - (c : ℂ) ^ 2 / (1 - z)

end StatMech.FrontierD
