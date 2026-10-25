/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualCrossings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDualEdges.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalDualCrossings
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

noncomputable def fkRectRawHorizontalCrossingRepresentative
    (R : FKRectTorus) (eta : R.Configuration)
    (C : {C : (fkRectOpenGraph R eta).ConnectedComponent //
      FKRectRawHorizontalCrossingComponent R eta C}) : Fin R.height :=
  Classical.choose C.2.1

end
end StatMech.FrontierD
