/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigEventLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
open scoped BigOperators
open SimpleGraph


namespace StatMech.FK

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def ecz_closeOff (omega : ConfigSpace (Sym2 V)) : ecz_ClosedOff G :=
  ⟨fun e => if he : e ∈ G.edgeFinset then omega e else false, by
    intro e he
    change (if _ : e ∈ G.edgeFinset then omega e else false) = false
    rw [dif_neg he]⟩

end
end StatMech.FK
