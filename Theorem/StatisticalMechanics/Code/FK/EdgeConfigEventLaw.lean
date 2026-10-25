/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigEventLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
import Def.StatisticalMechanics.Code.FK.EdgeConfigEventLaw
open scoped BigOperators
open SimpleGraph


namespace StatMech.FK

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp] theorem ecz_closeOff_apply_edge
    (omega : ConfigSpace (Sym2 V)) {e : Sym2 V}
    (he : e ∈ G.edgeFinset) :
    (ecz_closeOff G omega).1 e = omega e := by
  change (if _ : e ∈ G.edgeFinset then omega e else false) = omega e
  rw [dif_pos he]

@[simp] theorem ecz_closeOff_val (omega : ecz_ClosedOff G) :
    ecz_closeOff G omega.1 = omega := by
  apply Subtype.ext
  funext e
  by_cases he : e ∈ G.edgeFinset
  · change (if _ : e ∈ G.edgeFinset then omega.1 e else false) = omega.1 e
    rw [dif_pos he]
  · change (if _ : e ∈ G.edgeFinset then omega.1 e else false) = omega.1 e
    rw [dif_neg he, omega.2 e he]


end
end StatMech.FK
