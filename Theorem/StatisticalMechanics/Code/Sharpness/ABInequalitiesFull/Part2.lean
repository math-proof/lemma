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
import Def.StatisticalMechanics.Code.Sharpness.ABInequalitiesFull.Part2
open MeasureTheory Set Finset
open scoped NNReal ENNReal


namespace StatMech

namespace Sharpness

open ConfigSpace StatMech SimpleGraph


set_option linter.unusedSectionVars false

variable {V : Type*} [DecidableEq V]


theorem sab_transfer_avoid_edges (G : SimpleGraph V) {ωS ω : ConfigSpace (Sym2 V)}
    (A : Set V) (x y : V) (hx : x ∈ A) (hy : y ∈ A) {u a : A}
    (hagreeOff : ∀ e, e ≠ s(x,y) → ωS e = ω e)
    (w : ((openSub G ωS).induce A).Walk u a)
    (hav : s((⟨x,hx⟩ : A), (⟨y,hy⟩ : A)) ∉ w.edges) :
    (sab_transfer_avoid G A x y hx hy hagreeOff w hav).edges = w.edges := by
  unfold sab_transfer_avoid
  rw [sab_inducedWalkTransfer_edges]


section PathSplit

variable {W : Type*} {H : SimpleGraph W}


theorem sab_path_head_edge (X b Y : W) (q : H.Walk X b) (hq : q.support.Nodup)
    (heY : s(X, Y) ∈ q.edges) :
    ∃ (h : H.Adj X Y) (r : H.Walk Y b), q = Walk.cons h r ∧ s(X, Y) ∉ r.edges := by
  have hnil : ¬ q.Nil := by
    intro hn; rw [Walk.edges_eq_nil.mpr hn] at heY; simp at heY
  obtain ⟨w, hadj, r, rfl⟩ := Walk.not_nil_iff.mp hnil
  rw [Walk.support_cons] at hq
  have hXr : X ∉ r.support := fun hmem => (List.nodup_cons.mp hq).1 hmem
  rw [Walk.edges_cons, List.mem_cons] at heY
  rcases heY with hhead | htail
  · rw [Sym2.eq_iff] at hhead
    rcases hhead with ⟨_, hw⟩ | ⟨hXw, hwX⟩
    · subst hw; exact ⟨hadj, r, rfl, fun hr => hXr (r.fst_mem_support_of_mem_edges hr)⟩
    · subst hXw; exact absurd hadj (H.irrefl)
  · exact absurd (r.fst_mem_support_of_mem_edges htail) hXr


theorem sab_path_split_edge (u b X Y : W) (p : H.Walk u b) (hp : p.IsPath)
    (he : s(X, Y) ∈ p.edges) :
    ∃ (p1 p2 : W), (s(p1, p2) = s(X, Y)) ∧
      ∃ (q1 : H.Walk u p1) (q2 : H.Walk p2 b),
        s(X, Y) ∉ q1.edges ∧ s(X, Y) ∉ q2.edges ∧
        q1.edges.Disjoint q2.edges ∧
        q1.edges ⊆ p.edges ∧ q2.edges ⊆ p.edges := by
  classical
  have hX : X ∈ p.support := p.fst_mem_support_of_mem_edges he
  set t := p.takeUntil X hX with ht
  set d := p.dropUntil X hX with hd
  have htpath : t.IsPath := hp.takeUntil hX
  have hdpath : d.IsPath := hp.dropUntil hX
  have hdisj : t.edges.Disjoint d.edges := hp.isTrail.disjoint_edges_takeUntil_dropUntil hX
  have hsub_t : t.edges ⊆ p.edges := p.edges_takeUntil_subset hX
  have hsub_d : d.edges ⊆ p.edges := p.edges_dropUntil_subset hX
  have hmem : s(X, Y) ∈ t.edges ∨ s(X, Y) ∈ d.edges := by
    have : s(X, Y) ∈ t.edges ++ d.edges := by
      rw [← Walk.edges_append, Walk.take_spec]; exact he
    exact List.mem_append.mp this
  rcases hmem with hmt | hmd
  · 
    have htr : t.reverse.support.Nodup := by
      rw [Walk.support_reverse, List.nodup_reverse]; exact htpath.support_nodup
    have htredge : s(X, Y) ∈ t.reverse.edges := by rw [Walk.edges_reverse]; simpa using hmt
    obtain ⟨hadj, r, htreq, hrnotin⟩ := sab_path_head_edge X u Y t.reverse htr htredge
    refine ⟨Y, X, Sym2.eq_swap, r.reverse, d, ?_, ?_, ?_, ?_, hsub_d⟩
    · rw [Walk.edges_reverse, List.mem_reverse]; exact hrnotin
    · intro hcon; exact hdisj hmt hcon
    · intro z hz1 hz2
      rw [Walk.edges_reverse, List.mem_reverse] at hz1
      have hzt : z ∈ t.edges := by
        have : z ∈ t.reverse.edges := by
          rw [htreq, Walk.edges_cons]; exact List.mem_cons_of_mem _ hz1
        rwa [Walk.edges_reverse, List.mem_reverse] at this
      exact hdisj hzt hz2
    · intro z hz
      rw [Walk.edges_reverse, List.mem_reverse] at hz
      have hzt : z ∈ t.edges := by
        have : z ∈ t.reverse.edges := by
          rw [htreq, Walk.edges_cons]; exact List.mem_cons_of_mem _ hz
        rwa [Walk.edges_reverse, List.mem_reverse] at this
      exact hsub_t hzt
  · 
    obtain ⟨hadj, r, hdeq, hrnotin⟩ := sab_path_head_edge X b Y d hdpath.support_nodup hmd
    refine ⟨X, Y, rfl, t, r, ?_, hrnotin, ?_, hsub_t, ?_⟩
    · intro hcon; exact hdisj hcon hmd
    · intro z hz1 hz2
      have hzd : z ∈ d.edges := by rw [hdeq, Walk.edges_cons]; exact List.mem_cons_of_mem _ hz2
      exact hdisj hz1 hzd
    · intro z hz
      have hzd : z ∈ d.edges := by rw [hdeq, Walk.edges_cons]; exact List.mem_cons_of_mem _ hz
      exact hsub_d hzd

end PathSplit


theorem sab_pivotal_subset_firstExit (G : SimpleGraph V) (A : Set V) (u : V) (B : Set V)
    (x y : V) (hu : u ∈ A) (hx : x ∈ A) (hy : y ∈ A) :
    {ω | IsPivotal s(x,y) (connEvent G A u B) ω} ⊆
      (disjointOccurrence (connEvent G A u {x}) (connEvent G A y B)) ∪
      (disjointOccurrence (connEvent G A u {y}) (connEvent G A x B)) := by
  classical
  intro ω hω
  
  obtain ⟨hclosed, hopen⟩ :=
    (isPivotal_iff_of_isIncreasing (isIncreasing_connEvent G A u B) ω).mp hω
  have hOagree : ∀ e, e ≠ s(x,y) → setOpen s(x,y) ω e = ω e := fun e h => sab_setOpen_eq_off h
  
  have hCagree : ∀ e, e ≠ s(x,y) → setOpen s(x,y) ω e = setClosed s(x,y) ω e := by
    intro e h; rw [sab_setClosed_eq_off h, sab_setOpen_eq_off h]
  
  obtain ⟨_, b, hb, hbB, hconn⟩ := hopen
  obtain ⟨p, hp⟩ := hconn.exists_isPath
  
  have hpe : s((⟨x, hx⟩ : A), (⟨y, hy⟩ : A)) ∈ p.edges := by
    by_contra hno
    have wC := sab_transfer_avoid G A x y hx hy hCagree p hno
    exact hclosed ⟨hu, b, hb, hbB, ⟨wC⟩⟩
  
  obtain ⟨p1, p2, hsplit, q1, q2, hq1av, hq2av, hqdisj, _, _⟩ :=
    sab_path_split_edge ⟨u, hu⟩ ⟨b, hb⟩ (⟨x, hx⟩ : A) (⟨y, hy⟩ : A) p hp hpe
  
  set wq1 := sab_transfer_avoid G A x y hx hy hOagree q1 hq1av with hwq1
  set wq2 := sab_transfer_avoid G A x y hx hy hOagree q2 hq2av with hwq2
  have he1 : wq1.edges = q1.edges := by
    rw [hwq1]; exact sab_transfer_avoid_edges G A x y hx hy hOagree q1 hq1av
  have he2 : wq2.edges = q2.edges := by
    rw [hwq2]; exact sab_transfer_avoid_edges G A x y hx hy hOagree q2 hq2av
  
  have hdisjES : Disjoint (sab_inducedEdgeSet G ω A wq1) (sab_inducedEdgeSet G ω A wq2) := by
    apply sab_inducedEdgeSet_disjoint
    intro z hz1 hz2
    rw [he1] at hz1; rw [he2] at hz2
    exact hqdisj hz1 hz2
  
  rw [Sym2.eq_iff] at hsplit
  rcases hsplit with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · 
    subst h1; subst h2
    exact Or.inl ⟨sab_inducedEdgeSet G ω A wq1, sab_inducedEdgeSet G ω A wq2, hdisjES,
      sab_occursOn_connEvent_of_walk G ω A hu hx wq1,
      sab_occursOn_connEventSet_of_walk G ω A B hy hb hbB wq2⟩
  · 
    subst h1; subst h2
    exact Or.inr ⟨sab_inducedEdgeSet G ω A wq1, sab_inducedEdgeSet G ω A wq2, hdisjES,
      sab_occursOn_connEvent_of_walk G ω A hu hy wq1,
      sab_occursOn_connEventSet_of_walk G ω A B hx hb hbB wq2⟩


theorem sab_pivotal_firstExit_increasing (G : SimpleGraph V) (A : Set V) (u : V) (B : Set V)
    (x y : V) (hu : u ∈ A) (hx : x ∈ A) (hy : y ∈ A) :
    IsIncreasing (disjointOccurrence (connEvent G A u {x}) (connEvent G A y B)) ∧
    IsIncreasing (disjointOccurrence (connEvent G A u {y}) (connEvent G A x B)) ∧
    {ω | IsPivotal s(x,y) (connEvent G A u B) ω} ⊆
      (disjointOccurrence (connEvent G A u {x}) (connEvent G A y B)) ∪
      (disjointOccurrence (connEvent G A u {y}) (connEvent G A x B)) :=
  ⟨disjointOccurrence_isIncreasing (isIncreasing_connEvent G A u {x}) (isIncreasing_connEvent G A y B),
   disjointOccurrence_isIncreasing (isIncreasing_connEvent G A u {y}) (isIncreasing_connEvent G A x B),
   sab_pivotal_subset_firstExit G A u B x y hu hx hy⟩

end Sharpness
end StatMech
