/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWalkHomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationWalkTransition
import Theorem.StatisticalMechanics.Code.Onsager.TorusLoopHomology.Part2
import Def.StatisticalMechanics.Code.Onsager.DecorationWalkHomology


namespace StatMech.Onsager

open BigOperators

instance ons_decCycleDartList_neZero {L : ℕ} {d : ons_Dart L}
    (q : (ons_decGraph L).Walk d d) :
    NeZero (ons_decCycleDartList q).length := by
  refine ⟨?_⟩
  simp [ons_decCycleDartList, ons_decCycleFirstReturn]

end StatMech.Onsager
