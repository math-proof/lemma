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
import Def.StatisticalMechanics.Code.Sharpness.ABInequalitiesFull
open MeasureTheory Set Finset
open scoped NNReal ENNReal


namespace StatMech

namespace Sharpness

open ConfigSpace StatMech SimpleGraph


set_option linter.unusedSectionVars false

variable {V : Type*} [DecidableEq V]


theorem sab_inducedWalkTransfer_edges (G : SimpleGraph V) {ω ω' : ConfigSpace (Sym2 V)}
    {A : Set V} {x y : A} (w : ((openSub G ω).induce A).Walk x y)
    (hagree : ∀ e ∈ sab_inducedEdgeSet G ω A w, ω e = ω' e) :
    (sab_inducedWalkTransfer G w hagree).edges = w.edges := by
  induction w with
  | nil => rfl
  | @cons a b c hadj p ih =>
    simp only [sab_inducedWalkTransfer]
    rw [Walk.edges_cons, Walk.edges_cons]; congr 1; apply ih


theorem sab_sym2_map_val_injective {A : Set V} :
    Function.Injective (Sym2.map (Subtype.val : A → V)) :=
  Sym2.map.injective Subtype.val_injective


theorem sab_inducedEdgeSet_avoid {G : SimpleGraph V} {ω : ConfigSpace (Sym2 V)} {A : Set V}
    {u a : A} (w : ((openSub G ω).induce A).Walk u a) {X Y : A}
    (hav : s(X, Y) ∉ w.edges) :
    s((X:V),(Y:V)) ∉ sab_inducedEdgeSet G ω A w := by
  rintro ⟨z, hz, heq⟩
  have : Sym2.map (Subtype.val) (s(X,Y)) = Sym2.map (Subtype.val) z := by
    rw [← heq]; simp [Sym2.map_mk]
  exact hav ((sab_sym2_map_val_injective this) ▸ hz)


theorem sab_inducedEdgeSet_disjoint (G : SimpleGraph V) (ω : ConfigSpace (Sym2 V)) (A : Set V)
    {x y x' y' : A} (p : ((openSub G ω).induce A).Walk x y)
    (q : ((openSub G ω).induce A).Walk x' y')
    (h : ∀ z, z ∈ p.edges → z ∈ q.edges → False) :
    Disjoint (sab_inducedEdgeSet G ω A p) (sab_inducedEdgeSet G ω A q) := by
  rw [Set.disjoint_left]
  rintro e ⟨zp, hzp, rfl⟩ ⟨zq, hzq, heq⟩
  exact h zp hzp ((sab_sym2_map_val_injective heq) ▸ hzq)


theorem sab_occursOn_connEvent_of_walk (G : SimpleGraph V) (ω : ConfigSpace (Sym2 V))
    (A : Set V) {u a : V} (hu : u ∈ A) (ha : a ∈ A)
    (w : ((openSub G ω).induce A).Walk ⟨u, hu⟩ ⟨a, ha⟩) :
    OccursOn (connEvent G A u {a}) (sab_inducedEdgeSet G ω A w) ω := by
  intro ω' hagree
  have hagree' : ∀ e ∈ sab_inducedEdgeSet G ω A w, ω e = ω' e := fun e he => (hagree e he).symm
  exact ⟨hu, a, ha, rfl, ⟨sab_inducedWalkTransfer G w hagree'⟩⟩


theorem sab_occursOn_connEventSet_of_walk (G : SimpleGraph V) (ω : ConfigSpace (Sym2 V))
    (A : Set V) {u b : V} (B : Set V) (hu : u ∈ A) (hb : b ∈ A) (hbB : b ∈ B)
    (w : ((openSub G ω).induce A).Walk ⟨u, hu⟩ ⟨b, hb⟩) :
    OccursOn (connEvent G A u B) (sab_inducedEdgeSet G ω A w) ω := by
  intro ω' hagree
  have hagree' : ∀ e ∈ sab_inducedEdgeSet G ω A w, ω e = ω' e := fun e he => (hagree e he).symm
  exact ⟨hu, b, hb, hbB, ⟨sab_inducedWalkTransfer G w hagree'⟩⟩


theorem sab_setOpen_eq_off {ω : ConfigSpace (Sym2 V)} {x y : V} {e : Sym2 V} (h : e ≠ s(x,y)) :
    setOpen s(x,y) ω e = ω e := setOpen_of_ne h ω


theorem sab_setClosed_eq_off {ω : ConfigSpace (Sym2 V)} {x y : V} {e : Sym2 V} (h : e ≠ s(x,y)) :
    setClosed s(x,y) ω e = ω e := setClosed_of_ne h ω


end Sharpness
end StatMech
