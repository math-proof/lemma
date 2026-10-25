/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheThermodynamicReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertexAntiferroelectricSeries.Part9
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

def sixVertexFourWidth (r k : ℕ) : ℕ := 4 * (r + k + 1)

end StatMech.FrontierD
