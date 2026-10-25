/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricProduct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheScattering.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheThermodynamicReduction.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricProduct.Part2
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

abbrev SixVertexSymmetricHalfFilledRoots :=
  (k : ℕ) → Fin (k + 1) → ℝ


end StatMech.FrontierD
