/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusNetFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetMonotonicity
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusConnected.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusNetFull.Part3
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

abbrev fkRectOrigin (R : FKRectTorus) : R.Vertex :=
  ((⟨0, R.width_pos⟩ : Fin R.width),
    (⟨0, R.height_pos⟩ : Fin R.height))

end
end StatMech.FrontierD
