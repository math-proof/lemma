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
open MeasureTheory Set Finset
open scoped NNReal ENNReal


namespace StatMech

namespace Sharpness

open ConfigSpace StatMech SimpleGraph


set_option linter.unusedSectionVars false

variable {V : Type*} [DecidableEq V]


def sab_inducedEdgeSet (G : SimpleGraph V) (ω : ConfigSpace (Sym2 V)) (A : Set V) {x y : A}
    (w : ((openSub G ω).induce A).Walk x y) : Set (Sym2 V) :=
  {e | ∃ z ∈ w.edges, e = Sym2.map Subtype.val z}


noncomputable def sab_inducedWalkTransfer (G : SimpleGraph V) {ω ω' : ConfigSpace (Sym2 V)}
    {A : Set V} {x y : A}
    (w : ((openSub G ω).induce A).Walk x y)
    (hagree : ∀ e ∈ sab_inducedEdgeSet G ω A w, ω e = ω' e) :
    ((openSub G ω').induce A).Walk x y := by
  induction w with
  | nil => exact Walk.nil
  | @cons a b c hadj p ih =>
    have hedges : ∀ e ∈ sab_inducedEdgeSet G ω A p, ω e = ω' e := by
      intro e he
      obtain ⟨z, hz, rfl⟩ := he
      exact hagree _ ⟨z, by simp [Walk.edges_cons, hz], rfl⟩
    have hadj' : ((openSub G ω').induce A).Adj a b := by
      have hcoord : ω s((a:V),(b:V)) = ω' s((a:V),(b:V)) := by
        apply hagree; exact ⟨s(a,b), by simp [Walk.edges_cons], by simp [Sym2.map_mk]⟩
      have : (openSub G ω').Adj (a:V) (b:V) := ⟨hadj.1, by rw [← hcoord]; exact hadj.2⟩
      exact induce_adj.2 this
    exact Walk.cons hadj' (ih hedges)


end Sharpness
end StatMech
