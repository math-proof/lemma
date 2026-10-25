/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInequalitiesFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.Russo
import Theorem.StatisticalMechanics.Code.Inequalities.BK.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterion.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.ABInequalitiesFull
open MeasureTheory Set Finset
open scoped NNReal ENNReal


namespace StatMech

namespace Sharpness

open ConfigSpace StatMech SimpleGraph


set_option linter.unusedSectionVars false

variable {V : Type*} [DecidableEq V]


noncomputable def sab_transfer_avoid (G : SimpleGraph V) {ωS ω : ConfigSpace (Sym2 V)}
    (A : Set V) (x y : V) (hx : x ∈ A) (hy : y ∈ A) {u a : A}
    (hagreeOff : ∀ e, e ≠ s(x,y) → ωS e = ω e)
    (w : ((openSub G ωS).induce A).Walk u a)
    (hav : s((⟨x,hx⟩ : A), (⟨y,hy⟩ : A)) ∉ w.edges) :
    ((openSub G ω).induce A).Walk u a := by
  apply sab_inducedWalkTransfer G w
  intro e he
  have hne : e ≠ s(x,y) := by
    intro hcon; subst hcon; exact sab_inducedEdgeSet_avoid w hav he
  exact hagreeOff e hne


end Sharpness
end StatMech
