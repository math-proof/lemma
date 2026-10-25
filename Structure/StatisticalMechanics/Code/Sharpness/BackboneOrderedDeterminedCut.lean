/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneOrderedDeterminedCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part6
open Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

structure shb_OrderedLocalTests (E B : Type*) [DecidableEq E] where
  order : List E
  order_nodup : order.Nodup
  exposure : E -> Set B
  test : (B -> Bool) -> E -> Bool
  test_local : ∀ omega eta e,
    (∀ b ∈ exposure e, omega b = eta b) -> test omega e = test eta e

end
end StatMech.Sharpness
