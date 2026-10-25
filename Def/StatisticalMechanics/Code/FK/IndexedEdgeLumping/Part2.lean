/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/IndexedEdgeLumping.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEquiv.Part2
import Abbrev.StatisticalMechanics.Code.FK.IndexedEdgeLumping
open Finset


namespace StatMech.FK

noncomputable section

variable {E A : Type*} [Fintype E] [DecidableEq E]
  [Fintype A] [DecidableEq A]


def indexedSplit (f : E → A) :
    (E → Bool) ≃ indexedFiberConfigs f :=
  Equiv.piCongrFiberwise (fun _ => Equiv.refl _)

end
end StatMech.FK
