/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part32
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStar.Part4
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainEvenPolynomial.Part9
open scoped BigOperators


namespace StatMech.FrontierA

open Finset SimpleGraph

open StatMech.Ising


@[simp] theorem kwOrderedSplitFinsetChainField_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G)
    (F : Finset (Sym2 (KWDartPort G))) (v : V) :
    kwOrderedSplitFinsetChainField G order F v 0 = 0 := by
  simp [kwOrderedSplitFinsetChainField]

@[simp] theorem kwOrderedSplitFinsetChainField_last
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G)
    (F : Finset (Sym2 (KWDartPort G))) (v : V) :
    kwOrderedSplitFinsetChainField G order F v
      (Fin.last (Fintype.card (KWOutgoingDart (G := G) v))) = 0 := by
  by_cases h : Fin.last (Fintype.card (KWOutgoingDart (G := G) v)) = 0
  · rw [h]
    exact kwOrderedSplitFinsetChainField_zero G order F v
  · simp [kwOrderedSplitFinsetChainField, h]

@[simp] theorem kwExternalPortBits_extract
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (F : Finset (Sym2 (KWDartPort G))) (p : KWDartPort G) :
    kwExternalPortBits G (kwOrderedSplitFinsetExternalBits G F) p =
      if s(p, kwOrderedMatchingNeighbor G p) ∈ F then 1 else 0 := by
  unfold kwExternalPortBits kwOrderedSplitFinsetExternalBits
  simp only [kwPortOfDart_dartOfPort]
  rfl

theorem kwOrderedSplitFinsetChainField_castSucc
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G)
    (F : Finset (Sym2 (KWDartPort G))) (v : V)
    (i : Fin (Fintype.card (KWOutgoingDart (G := G) v)))
    (hpos : 0 < i.val) :
    kwOrderedSplitFinsetChainField G order F v i.castSucc =
      if s(kwPortAtOrderedRank order v
          ⟨i.val - 1, by omega⟩,
        kwPortAtOrderedRank order v i) ∈ F then 1 else 0 := by
  unfold kwOrderedSplitFinsetChainField
  have hzero : i.castSucc ≠ 0 := by
    apply Fin.ne_of_val_ne
    simp only [Fin.val_castSucc, Fin.val_zero]
    omega
  have hlast : i.castSucc ≠ Fin.last
      (Fintype.card (KWOutgoingDart (G := G) v)) := by
    apply Fin.ne_of_val_ne
    simp only [Fin.val_castSucc, Fin.val_last]
    exact Nat.ne_of_lt i.isLt
  rw [dif_neg hzero, dif_neg hlast]
  congr 3

theorem kwOrderedSplitFinsetChainField_succ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G)
    (F : Finset (Sym2 (KWDartPort G))) (v : V)
    (i : Fin (Fintype.card (KWOutgoingDart (G := G) v)))
    (hnext : i.val + 1 < Fintype.card (KWOutgoingDart (G := G) v)) :
    kwOrderedSplitFinsetChainField G order F v i.succ =
      if s(kwPortAtOrderedRank order v i,
        kwPortAtOrderedRank order v ⟨i.val + 1, hnext⟩) ∈ F
      then 1 else 0 := by
  unfold kwOrderedSplitFinsetChainField
  have hzero : i.succ ≠ 0 := by
    apply Fin.ne_of_val_ne
    simp
  have hlast : i.succ ≠ Fin.last
      (Fintype.card (KWOutgoingDart (G := G) v)) := by
    apply Fin.ne_of_val_ne
    simp only [Fin.val_succ, Fin.val_last]
    exact Nat.ne_of_lt hnext
  rw [dif_neg hzero, dif_neg hlast]
  congr 3

theorem kw_evenSubgraph_neighbor_sum_zero
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (F : Finset (Sym2 W)) (hF : F ∈ evenSubgraphs H) (v : W) :
    ∑ w ∈ H.neighborFinset v,
      (if s(v, w) ∈ F then (1 : ZMod 2) else 0) = 0 := by
  have hdata := hF
  rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset] at hdata
  have hFeq : F = H.edgeFinset.filter (fun edge => edge ∈ F) := by
    ext edge
    simp only [Finset.mem_filter]
    constructor
    · intro hedge
      exact ⟨hdata.1 hedge, hedge⟩
    · exact And.right
  have hcast : ((incCount F v : ℕ) : ZMod 2) = 0 := by
    apply (CharP.cast_eq_zero_iff (ZMod 2) 2 _).mpr
    exact even_iff_two_dvd.mp (hdata.2 v)
  have hsum := kw_cast_incCount_filter_eq_neighbor_sum H
    (fun edge => edge ∈ F) v
  rw [← hFeq, hcast] at hsum
  exact hsum.symm


theorem kwOrderedPortSplitAdjBit_extract
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G)
    (F : Finset (Sym2 (KWDartPort G))) {p q : KWDartPort G}
    (hpq : (kwOrderedDartPortSplitGraph G order).Adj p q) :
    kwOrderedPortSplitAdjBit G order
      (kwOrderedSplitFinsetExternalBits G F)
      (kwOrderedSplitFinsetChainField G order F) p q =
        if s(p, q) ∈ F then 1 else 0 := by
  rw [kwOrderedDartPortSplitGraph_adj] at hpq
  rcases hpq with hext | hint
  · have hq : q = kwOrderedMatchingNeighbor G p := by
      apply kwDartOfPort_injective G
      rw [hext]
      simp
    subst q
    rw [kwOrderedPortSplitAdjBit_matching, kwExternalPortBits_extract]
  · have hnotext : ¬kwDartOfPort G q = (kwDartOfPort G p).symm := by
      intro hext
      have hfirst := congrArg (fun d : G.Dart => d.fst) hext
      have hpfirst := kwDartOfPort_fst G p
      have hqfirst := kwDartOfPort_fst G q
      apply (kwDartOfPort G p).fst_ne_snd
      calc
        (kwDartOfPort G p).fst = p.1 := hpfirst
        _ = q.1 := hint.1
        _ = (kwDartOfPort G q).fst := hqfirst.symm
        _ = ((kwDartOfPort G p).symm).fst := hfirst
        _ = (kwDartOfPort G p).snd := rfl
    unfold kwOrderedPortSplitAdjBit
    rw [if_neg hnotext]
    let i := order p.1 p.2
    have hrankp : kwOrderedPortRank order p = i.val := rfl
    have hp : p = kwPortAtOrderedRank order p.1 i := by
      apply kwDartPort_eq_of_fst_of_orderRank
        (p := p) (q := kwPortAtOrderedRank order p.1 i) order rfl
      change i.val = ((order p.1) ((order p.1).symm i)).val
      rw [(order p.1).apply_symm_apply]
    rcases hint.2 with hsucc | hpred
    · have hnext : i.val + 1 <
          Fintype.card (KWOutgoingDart (G := G) p.1) := by
        have hqbound : kwOrderedPortRank order q <
            Fintype.card (KWOutgoingDart (G := G) q.1) :=
          (order q.1 q.2).isLt
        rw [← hrankp, hsucc]
        simpa [hint.1] using hqbound
      have hq : q = kwPortAtOrderedRank order p.1
          ⟨i.val + 1, hnext⟩ := by
        apply kwDartPort_eq_of_fst_of_orderRank
          (p := q) (q := kwPortAtOrderedRank order p.1
            ⟨i.val + 1, hnext⟩) order hint.1.symm
        change kwOrderedPortRank order q =
          ((order p.1) ((order p.1).symm ⟨i.val + 1, hnext⟩)).val
        rw [(order p.1).apply_symm_apply]
        change kwOrderedPortRank order q = i.val + 1
        omega
      have hnotpred : ¬(kwOrderedPortRank order q + 1 =
          kwOrderedPortRank order p) := by omega
      rw [if_neg hnotpred,
        kwOrderedSplitFinsetChainField_succ G order F p.1 i hnext]
      rw [← hq]
      rw [← hp]
    · have hpos : 0 < i.val := by
        rw [← hrankp, ← hpred]
        omega
      have hq : q = kwPortAtOrderedRank order p.1
          ⟨i.val - 1, by omega⟩ := by
        apply kwDartPort_eq_of_fst_of_orderRank
          (p := q) (q := kwPortAtOrderedRank order p.1
            ⟨i.val - 1, by omega⟩) order hint.1.symm
        change kwOrderedPortRank order q =
          ((order p.1) ((order p.1).symm ⟨i.val - 1, by omega⟩)).val
        rw [(order p.1).apply_symm_apply]
        change kwOrderedPortRank order q = i.val - 1
        omega
      rw [if_pos hpred,
        kwOrderedSplitFinsetChainField_castSucc G order F p.1 i hpos]
      rw [← hq, Sym2.eq_swap]
      rw [← hp]

theorem kw_fin2_solve_recurrence (external left right : Fin 2)
    (h : external + left + right = 0) :
    right = left + external := by
  calc
    right = right + 0 := (add_zero _).symm
    _ = right + (external + left + right) := by rw [h]
    _ = (right + right) + (external + left) := by ac_rfl
    _ = external + left := by rw [kw_fin_two_self_add, zero_add]
    _ = left + external := add_comm _ _


theorem kwOrderedSplitFinset_globalEven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G)
    (F : Finset (Sym2 (KWDartPort G)))
    (hF : F ∈ evenSubgraphs (kwOrderedDartPortSplitGraph G order)) :
    KWOrderedGlobalPortChainEven G order
      (kwOrderedSplitFinsetExternalBits G F)
      (kwOrderedSplitFinsetChainField G order F) := by
  intro v
  let b := kwOrderedSplitFinsetExternalBits G F
  let y := kwOrderedSplitFinsetChainField G order F
  refine ⟨kwOrderedSplitFinsetChainField_zero G order F v, ?_,
    kwOrderedSplitFinsetChainField_last G order F v⟩
  intro i
  let p := kwPortAtOrderedRank order v i
  have hsumZ := kw_evenSubgraph_neighbor_sum_zero
    (kwOrderedDartPortSplitGraph G order) F hF p
  have hsumFin :
      (∑ q ∈ (kwOrderedDartPortSplitGraph G order).neighborFinset p,
        (if s(p, q) ∈ F then (1 : Fin 2) else 0)) = 0 := by
    simpa only using hsumZ
  have hadjEq :
      (∑ q ∈ (kwOrderedDartPortSplitGraph G order).neighborFinset p,
        kwOrderedPortSplitAdjBit G order b y p q) =
      ∑ q ∈ (kwOrderedDartPortSplitGraph G order).neighborFinset p,
        (if s(p, q) ∈ F then (1 : Fin 2) else 0) := by
    apply Finset.sum_congr rfl
    intro q hq
    exact kwOrderedPortSplitAdjBit_extract G order F
      ((SimpleGraph.mem_neighborFinset _ _ _).mp hq)
  have hadj :
      (∑ q ∈ (kwOrderedDartPortSplitGraph G order).neighborFinset p,
        kwOrderedPortSplitAdjBit G order b y p q) = 0 :=
    hadjEq.trans hsumFin
  have hinc : kwOrderedPortSplitIncidence G order b y p = 0 := by
    rw [← kwOrderedPortSplit_neighbor_sum]
    exact hadj
  unfold kwOrderedPortSplitIncidence at hinc
  dsimp only [p, kwPortAtOrderedRank, kwOrderedPortRank] at hinc
  let j := (order v) ((order v).symm i)
  have hj : j = i := (order v).apply_symm_apply i
  change ((kwExternalPortBits G b (kwPortAtOrderedRank order v i) +
      if j.val = 0 then 0 else y v j.castSucc) +
      if j.val + 1 = Fintype.card (KWOutgoingDart (G := G) v) then 0
      else y v j.succ) = 0 at hinc
  have hleft :
      (if j.val = 0 then 0 else y v j.castSucc) = y v j.castSucc := by
    by_cases hzero : j.val = 0
    · rw [if_pos hzero]
      symm
      have hi : j.castSucc = (0 : Fin
          (Fintype.card (KWOutgoingDart (G := G) v) + 1)) := Fin.ext hzero
      rw [hi]
      exact kwOrderedSplitFinsetChainField_zero G order F v
    · rw [if_neg hzero]
  have hright :
      (if j.val + 1 = Fintype.card (KWOutgoingDart (G := G) v) then 0
        else y v j.succ) = y v j.succ := by
    by_cases hlast : j.val + 1 =
        Fintype.card (KWOutgoingDart (G := G) v)
    · rw [if_pos hlast]
      symm
      have hi : j.succ = Fin.last
          (Fintype.card (KWOutgoingDart (G := G) v)) := Fin.ext hlast
      rw [hi]
      exact kwOrderedSplitFinsetChainField_last G order F v
    · rw [if_neg hlast]
  rw [hleft, hright] at hinc
  have hrec : y v j.succ = y v j.castSucc +
      kwExternalPortBits G b (kwPortAtOrderedRank order v i) :=
    kw_fin2_solve_recurrence _ _ _ hinc
  have hsucc := congrArg (fun k : Fin
      (Fintype.card (KWOutgoingDart (G := G) v)) => y v k.succ) hj
  have hcast := congrArg (fun k : Fin
      (Fintype.card (KWOutgoingDart (G := G) v)) => y v k.castSucc) hj
  change y v i.succ = y v i.castSucc +
    kwExternalPortBits G b (kwPortAtOrderedRank order v i)
  calc
    y v i.succ = y v j.succ := hsucc.symm
    _ = y v j.castSucc +
        kwExternalPortBits G b (kwPortAtOrderedRank order v i) := hrec
    _ = y v i.castSucc +
        kwExternalPortBits G b (kwPortAtOrderedRank order v i) :=
      congrArg (fun z => z +
        kwExternalPortBits G b (kwPortAtOrderedRank order v i)) hcast


theorem kwOrderedSplitEdges_extract
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G)
    (F : Finset (Sym2 (KWDartPort G)))
    (hF : F ∈ evenSubgraphs (kwOrderedDartPortSplitGraph G order)) :
    kwOrderedSplitEdges G order
      (kwOrderedSplitFinsetExternalBits G F)
      (kwOrderedSplitFinsetChainField G order F) = F := by
  have hdata := hF
  rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset] at hdata
  ext edge
  induction edge using Sym2.inductionOn with
  | _ p q =>
      by_cases hedge : s(p, q) ∈
          (kwOrderedDartPortSplitGraph G order).edgeFinset
      · have hpq : (kwOrderedDartPortSplitGraph G order).Adj p q :=
          SimpleGraph.mem_edgeFinset.mp hedge
        have hbit := kwOrderedPortSplitAdjBit_extract G order F hpq
        have hedgeBit : kwOrderedSplitEdgeBitValue G order
            (kwOrderedSplitFinsetExternalBits G F)
            (kwOrderedSplitFinsetChainField G order F) s(p, q) =
            kwOrderedPortSplitAdjBit G order
              (kwOrderedSplitFinsetExternalBits G F)
              (kwOrderedSplitFinsetChainField G order F) p q := by
          let d : (kwOrderedDartPortSplitGraph G order).Dart :=
            ⟨(p, q), hpq⟩
          exact kwOrderedSplitEdgeBitValue_edge G order _ _ d
        rw [kwOrderedSplitEdges, Finset.mem_filter, and_iff_right hedge,
          hedgeBit, hbit]
        simp
      · have hnotF : s(p, q) ∉ F := fun h => hedge (hdata.1 h)
        simp [kwOrderedSplitEdges, hedge, hnotF]


theorem kwOrderedSplitFinsetExternalBits_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (b : KWDartEdgeBits G)
    (y : KWPortChainField G) :
    kwOrderedSplitFinsetExternalBits G
      (kwOrderedSplitEdges G order b y) = b := by
  apply Subtype.ext
  funext d
  let delta := (kwOrderedExternalSplitDartOfDart G order d).1
  change (if s(kwPortOfDart G d, kwPortOfDart G d.symm) ∈
      kwOrderedSplitEdges G order b y then 1 else 0) = b.1 d
  have hedge : s(kwPortOfDart G d, kwPortOfDart G d.symm) = delta.edge := by
    rfl
  rw [hedge]
  simp only [mem_kwOrderedSplitEdges_iff G order b y delta]
  have hmatch : delta.snd = kwOrderedMatchingNeighbor G delta.fst := by
    apply kwDartOfPort_injective G
    simp [delta, kwOrderedMatchingNeighbor]
  rw [hmatch, kwOrderedPortSplitAdjBit_matching]
  have hbit : kwExternalPortBits G b delta.fst = b.1 d := by
    simp [delta, kwExternalPortBits]
  rw [hbit]
  exact kw_fin2_indicator_eq _


end StatMech.FrontierA
