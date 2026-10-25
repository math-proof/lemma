/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheThermodynamicReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheThermodynamicReduction.Part3
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable def sixVertexBalancedSectorPartitionSum
    (N M : ℕ) (c : ℝ) : ℝ :=
  Matrix.trace (sixVertexSectorTransfer N (N / 2) c ^ M)


noncomputable def sixVertexBalancedAreaDensity (c : ℝ) (k M : ℕ) : ℝ :=
  Real.log (sixVertexBalancedSectorPartitionSum (sixVertexFourWidth 0 k) M c) /
    ((sixVertexFourWidth 0 k : ℝ) * (M : ℝ))


end StatMech.FrontierD
