/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheThermodynamicReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part9
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheThermodynamicReduction.Part2
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

theorem sixVertexLambdaAlongFour_pos {c : ℝ} (hc : 0 < c) (r k : ℕ) :
    0 < sixVertexLambdaAlongFour c r k := by
  exact (sixVertexLambda_isPerronFrobenius
    (sixVertexFourWidth r k) r (sixVertexFourWidth_even r k)
    (sixVertexFourWidth_charge_le r k) hc).1


end StatMech.FrontierD
