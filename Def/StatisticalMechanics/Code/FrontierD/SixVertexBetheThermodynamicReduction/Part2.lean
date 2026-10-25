/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheThermodynamicReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheThermodynamicReduction
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable def sixVertexLambdaAlongFour (c : ℝ) (r k : ℕ) : ℝ :=
  sixVertexLambda (sixVertexFourWidth r k) r
    (sixVertexFourWidth_even r k) (sixVertexFourWidth_charge_le r k) c

end StatMech.FrontierD
