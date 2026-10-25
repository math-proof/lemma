/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheThermodynamicReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheThermodynamicReduction.Part2
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable def sixVertexCentralWidthRate (c : ℝ) (k : ℕ) : ℝ :=
  Real.log (sixVertexLambdaAlongFour c 0 k) / (sixVertexFourWidth 0 k : ℝ)


noncomputable def sixVertexFixedChargeRatio (c : ℝ) (r k : ℕ) : ℝ :=
  sixVertexLambdaAlongFour c r k /
    sixVertexLambda (sixVertexFourWidth r k) 0
      (sixVertexFourWidth_even r k) (Nat.zero_le _) c


noncomputable def sixVertexFixedChargeLogRatio (c : ℝ) (r k : ℕ) : ℝ :=
  Real.log (sixVertexFixedChargeRatio c r k)

end StatMech.FrontierD
