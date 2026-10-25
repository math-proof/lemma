/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusRandomCluster.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectTorusMedial.Part5
open scoped BigOperators


namespace StatMech.FrontierD

noncomputable section

noncomputable instance fkRectOpenGraphDecidableRel
    (R : FKRectTorus) (omega : R.Configuration) :
    DecidableRel (fkRectOpenGraph R omega).Adj := Classical.decRel _


end
end StatMech.FrontierD
