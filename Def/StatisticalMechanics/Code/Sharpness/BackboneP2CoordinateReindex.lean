/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP2CoordinateReindex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialP2Reindex.Part3
import Instance.StatisticalMechanics.Code.Sharpness.BackboneP2CoordinateReindex
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneP2CoordinateReindex

open BackboneLabeledSwitching

open BackbonePartialP2Reindex

variable {H G : SimpleGraph V}


noncomputable def extendFlux (_hHG : H ≤ G)
    (r : H.edgeFinset -> Nat) : G.edgeFinset -> Nat := fun e =>
  if he : e.1 ∈ H.edgeFinset then r ⟨e.1, he⟩ else 0

end BackboneP2CoordinateReindex
end
end StatMech.Sharpness
