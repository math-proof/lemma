/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonEmbedding.Part5
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonParity


namespace StatMech.FrontierD

open StatMech.Onsager

open StatMech.Onsager.BaseCase

noncomputable section

instance fkRectBlackOrbitMedialRibbonWord_length_neZero
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    NeZero (fkRectBlackOrbitMedialRibbonWord R omega d).length :=
  ⟨(List.length_pos_iff_ne_nil.mpr
    (fkRectBlackOrbitMedialRibbonWord_nonempty R omega d)).ne'⟩

end
end StatMech.FrontierD
