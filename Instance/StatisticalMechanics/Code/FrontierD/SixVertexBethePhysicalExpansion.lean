/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion.Part12
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

instance sixVertexForwardInterlacedDecidable {N : Nat}
    (x y : SixVertexRow N) : Decidable (SixVertexForwardInterlaced x y) :=
  Classical.propDecidable _

end
end StatMech.FrontierD
