/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronTruncation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronBulk.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronTruncation.Part5
open Filter Topology


namespace StatMech.FrontierD

noncomputable section

noncomputable def sixVertexCanonicalDensityPerronRootAverageLimit
    {c : Real} (hc : 2 < c) : Real :=
  Classical.choose (exists_sixVertexCanonicalDensityPerronRootAverage_limit hc)

end
end StatMech.FrontierD
