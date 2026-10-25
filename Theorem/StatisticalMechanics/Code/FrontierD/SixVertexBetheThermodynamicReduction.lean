/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheThermodynamicReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part9
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBetheThermodynamicReduction
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

theorem sixVertexFourWidth_pos (r k : ℕ) : 0 < sixVertexFourWidth r k := by
  unfold sixVertexFourWidth
  omega

theorem sixVertexFourWidth_even (r k : ℕ) : Even (sixVertexFourWidth r k) := by
  unfold sixVertexFourWidth Even
  use 2 * (r + k + 1)
  omega

theorem sixVertexFourWidth_charge_le (r k : ℕ) :
    r ≤ sixVertexFourWidth r k / 2 := by
  unfold sixVertexFourWidth
  omega


end StatMech.FrontierD
