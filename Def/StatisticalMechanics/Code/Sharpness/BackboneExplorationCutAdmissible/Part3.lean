/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationCutAdmissible.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part12
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationCutAdmissible.Part2
open SimpleGraph Finset
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def shb_generatedExplorationFiberMass
    (beta : Real) (J : Sym2 V -> Real) : shb_ExplorationFiberMass V
  | d, [] => currentSum d.graph beta J ∅
  | d, s :: ss =>
      if s ∈ d.active then
        shb_segmentNum beta J d s *
            shb_generatedExplorationFiberMass beta J
              (shb_BackboneExplorationDomain.advance d s) ss /
          currentSum (shb_BackboneExplorationDomain.advance d s).graph beta J ∅
      else 0


end
end StatMech.Sharpness
