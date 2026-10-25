/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneOrderedDeterminedCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part6
import Structure.StatisticalMechanics.Code.Sharpness.BackboneOrderedDeterminedCut.Part2
open Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

namespace shb_OrderedLocalExploration

variable {D E B : Type*} [DecidableEq E]


def Selects (X : shb_OrderedLocalExploration D E B)
    (omega : B -> Bool) : D -> List E -> Prop
  | _, [] => True
  | d, e :: es =>
      (X.tests d).order.find? ((X.tests d).test omega) = some e ∧
        X.Selects omega (X.advance d e) es


def traceCut (X : shb_OrderedLocalExploration D E B) : D -> List E -> Set B
  | _, [] => ∅
  | d, e :: es =>
      (X.tests d).determinedCut e ∪ X.traceCut (X.advance d e) es

end shb_OrderedLocalExploration
end
end StatMech.Sharpness
