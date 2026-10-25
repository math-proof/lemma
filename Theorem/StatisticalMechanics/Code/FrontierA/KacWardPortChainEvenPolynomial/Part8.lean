/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part32
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStar.Part4
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainEvenPolynomial.Part8
open scoped BigOperators


namespace StatMech.FrontierA

open Finset SimpleGraph

open StatMech.Ising


@[simp] theorem mem_kwOrderedSplitEdges_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (b : KWDartEdgeBits G)
    (y : KWPortChainField G)
    (d : (kwOrderedDartPortSplitGraph G order).Dart) :
    d.edge ∈ kwOrderedSplitEdges G order b y ↔
      kwOrderedPortSplitAdjBit G order b y d.fst d.snd = 1 := by
  simp [kwOrderedSplitEdges]


theorem kw_fin_sum_adjacent {n : ℕ} (i : Fin n) (left right : Fin 2) :
    (∑ j ∈ (Finset.univ.filter fun j : Fin n =>
        i.val + 1 = j.val ∨ j.val + 1 = i.val),
      if j.val + 1 = i.val then left else right) =
      (if i.val = 0 then 0 else left) +
        (if i.val + 1 = n then 0 else right) := by
  classical
  by_cases hzero : i.val = 0
  · by_cases hlast : i.val + 1 = n
    · have hempty : (Finset.univ.filter fun j : Fin n =>
          i.val + 1 = j.val ∨ j.val + 1 = i.val) = ∅ := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        simp
        omega
      rw [hempty]
      rw [Finset.sum_empty, if_pos hzero, if_pos hlast, add_zero]
    · have hsucc : i.val + 1 < n := by omega
      let next : Fin n := ⟨i.val + 1, hsucc⟩
      have hsingle : (Finset.univ.filter fun j : Fin n =>
          i.val + 1 = j.val ∨ j.val + 1 = i.val) = {next} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        constructor
        · intro h
          apply Fin.ext
          rcases h with h | h <;> dsimp only [next] <;> omega
        · rintro rfl
          exact Or.inl rfl
      rw [hsingle, Finset.sum_singleton]
      have hnotPred : ¬(next.val + 1 = i.val) := by
        dsimp only [next]
        omega
      rw [if_neg hnotPred, if_pos hzero, if_neg hlast, zero_add]
  · have hpos : 0 < i.val := by omega
    let previous : Fin n := ⟨i.val - 1, by omega⟩
    by_cases hlast : i.val + 1 = n
    · have hsingle : (Finset.univ.filter fun j : Fin n =>
          i.val + 1 = j.val ∨ j.val + 1 = i.val) = {previous} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        constructor
        · intro h
          apply Fin.ext
          rcases h with h | h <;> dsimp only [previous] <;> omega
        · rintro rfl
          right
          dsimp only [previous]
          omega
      rw [hsingle, Finset.sum_singleton]
      have hpred : previous.val + 1 = i.val := by
        dsimp only [previous]
        omega
      rw [if_pos hpred, if_neg hzero, if_pos hlast, add_zero]
    · have hsucc : i.val + 1 < n := by omega
      let next : Fin n := ⟨i.val + 1, hsucc⟩
      have hne : previous ≠ next := by
        intro h
        have := congrArg Fin.val h
        dsimp only [previous, next] at this
        omega
      have hpair : (Finset.univ.filter fun j : Fin n =>
          i.val + 1 = j.val ∨ j.val + 1 = i.val) =
          {previous, next} := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro h
          rcases h with h | h
          · right
            apply Fin.ext
            simpa [next] using h.symm
          · left
            apply Fin.ext
            dsimp only [previous]
            omega
        · rintro (rfl | rfl)
          · right
            dsimp only [previous]
            omega
          · left
            rfl
      have hpred : previous.val + 1 = i.val := by
        dsimp only [previous]
        omega
      have hnotPred : ¬(next.val + 1 = i.val) := by
        dsimp only [next]
        omega
      rw [hpair, Finset.sum_insert (by simpa using hne),
        Finset.sum_singleton, if_pos hpred, if_neg hnotPred,
        if_neg hzero, if_neg hlast]


theorem kwOrderedInternalNeighborFinset_eq_image
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (p : KWDartPort G) :
    kwOrderedInternalNeighborFinset G order p =
      (Finset.univ.filter fun j :
        Fin (Fintype.card (KWOutgoingDart (G := G) p.1)) =>
          kwOrderedPortRank order p + 1 = j.val ∨
            j.val + 1 = kwOrderedPortRank order p).image
        (kwPortAtOrderedRank order p.1) := by
  ext q
  rw [mem_kwOrderedInternalNeighborFinset, Finset.mem_image]
  constructor
  · rintro ⟨hfirst, hrank⟩
    let j : Fin (Fintype.card (KWOutgoingDart (G := G) p.1)) :=
      ⟨kwOrderedPortRank order q, by
        change (order q.1 q.2).val < _
        simpa [hfirst] using (order q.1 q.2).isLt⟩
    refine ⟨j, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [j] using hrank
    · rcases p with ⟨v, i⟩
      rcases q with ⟨w, k⟩
      dsimp only at hfirst ⊢
      subst w
      simp [kwPortAtOrderedRank, j, kwOrderedPortRank]
  · rintro ⟨j, hj, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    constructor
    · rfl
    · have hrank : kwOrderedPortRank order
          (kwPortAtOrderedRank order p.1 j) = j.val := by
        change ((order p.1) ((order p.1).symm j)).val = j.val
        exact congrArg Fin.val ((order p.1).apply_symm_apply j)
      rw [hrank]
      exact hj

theorem kwPortAtOrderedRank_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (order : KWPortOrder G) (v : V) :
    Function.Injective (kwPortAtOrderedRank order v) := by
  intro i j h
  have hsecond : (order v).symm i = (order v).symm j :=
    HEq.eq (Sigma.ext_iff.mp h).2
  exact (order v).symm.injective hsecond


theorem kwOrderedInternalNeighbor_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (b : KWDartEdgeBits G)
    (y : KWPortChainField G) (p : KWDartPort G) :
    (∑ q ∈ kwOrderedInternalNeighborFinset G order p,
        kwOrderedPortSplitAdjBit G order b y p q) =
      (if kwOrderedPortRank order p = 0 then 0
        else y p.1 (order p.1 p.2).castSucc) +
      (if kwOrderedPortRank order p + 1 =
          Fintype.card (KWOutgoingDart (G := G) p.1) then 0
        else y p.1 (order p.1 p.2).succ) := by
  classical
  rw [kwOrderedInternalNeighborFinset_eq_image]
  rw [Finset.sum_image]
  · let i := order p.1 p.2
    have hrankp : kwOrderedPortRank order p = i.val := rfl
    have hterm (j : Fin (Fintype.card (KWOutgoingDart (G := G) p.1)))
        (hj : j ∈ Finset.univ.filter fun j =>
          kwOrderedPortRank order p + 1 = j.val ∨
            j.val + 1 = kwOrderedPortRank order p) :
        kwOrderedPortSplitAdjBit G order b y p
            (kwPortAtOrderedRank order p.1 j) =
          if j.val + 1 = i.val then y p.1 i.castSucc
          else y p.1 i.succ := by
      have hext : ¬kwDartOfPort G (kwPortAtOrderedRank order p.1 j) =
          (kwDartOfPort G p).symm := by
        intro h
        have hfirst : p.1 = (kwDartOfPort G p).snd := by
          calc
            p.1 = (kwPortAtOrderedRank order p.1 j).1 := rfl
            _ = (kwDartOfPort G
                (kwPortAtOrderedRank order p.1 j)).fst :=
              (kwDartOfPort_fst G _).symm
            _ = ((kwDartOfPort G p).symm).fst :=
              congrArg (fun d : G.Dart => d.fst) h
            _ = (kwDartOfPort G p).snd := rfl
        apply (kwDartOfPort G p).fst_ne_snd
        calc
          (kwDartOfPort G p).fst = p.1 := kwDartOfPort_fst G p
          _ = (kwDartOfPort G p).snd := hfirst
      unfold kwOrderedPortSplitAdjBit
      rw [if_neg hext]
      have hrankj : kwOrderedPortRank order
          (kwPortAtOrderedRank order p.1 j) = j.val := by
        change ((order p.1) ((order p.1).symm j)).val = j.val
        exact congrArg Fin.val ((order p.1).apply_symm_apply j)
      rw [hrankj, hrankp]
    calc
      (∑ x ∈ Finset.univ.filter fun j :
          Fin (Fintype.card (KWOutgoingDart (G := G) p.1)) =>
            kwOrderedPortRank order p + 1 = j.val ∨
              j.val + 1 = kwOrderedPortRank order p,
          kwOrderedPortSplitAdjBit G order b y p
            (kwPortAtOrderedRank order p.1 x)) =
          ∑ x ∈ Finset.univ.filter fun j :
            Fin (Fintype.card (KWOutgoingDart (G := G) p.1)) =>
              i.val + 1 = j.val ∨ j.val + 1 = i.val,
            if x.val + 1 = i.val then y p.1 i.castSucc
            else y p.1 i.succ := by
        apply Finset.sum_congr
        · ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [hrankp]
        · intro j hj
          apply hterm j
          simpa [hrankp] using hj
      _ = (if i.val = 0 then 0 else y p.1 i.castSucc) +
          (if i.val + 1 = Fintype.card
              (KWOutgoingDart (G := G) p.1) then 0
            else y p.1 i.succ) :=
        kw_fin_sum_adjacent i (y p.1 i.castSucc) (y p.1 i.succ)
      _ = _ := by rfl
  · intro a ha c hc hac
    exact kwPortAtOrderedRank_injective order p.1 hac

@[simp] theorem kwOrderedPortSplitAdjBit_matching
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (b : KWDartEdgeBits G)
    (y : KWPortChainField G) (p : KWDartPort G) :
    kwOrderedPortSplitAdjBit G order b y p
      (kwOrderedMatchingNeighbor G p) = kwExternalPortBits G b p := by
  unfold kwOrderedPortSplitAdjBit
  rw [if_pos]
  simp [kwOrderedMatchingNeighbor]


theorem kwOrderedPortSplit_neighbor_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (b : KWDartEdgeBits G)
    (y : KWPortChainField G) (p : KWDartPort G) :
    (∑ q ∈ (kwOrderedDartPortSplitGraph G order).neighborFinset p,
      kwOrderedPortSplitAdjBit G order b y p q) =
        kwOrderedPortSplitIncidence G order b y p := by
  rw [kwOrderedSplit_neighborFinset,
    Finset.sum_insert (kwOrderedMatchingNeighbor_not_mem_internal G order p),
    kwOrderedPortSplitAdjBit_matching,
    kwOrderedInternalNeighbor_sum]
  unfold kwOrderedPortSplitIncidence
  abel


theorem kwOrderedSplitEdges_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (b : KWDartEdgeBits G)
    (y : KWPortChainField G)
    (hy : KWOrderedGlobalPortChainEven G order b y) :
    kwOrderedSplitEdges G order b y ∈
      evenSubgraphs (kwOrderedDartPortSplitGraph G order) := by
  rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · exact Finset.filter_subset _ _
  · intro p
    apply even_iff_two_dvd.mpr
    apply (CharP.cast_eq_zero_iff (ZMod 2) 2 _).mp
    have hsum := kw_cast_incCount_filter_eq_neighbor_sum
      (kwOrderedDartPortSplitGraph G order)
      (fun edge => kwOrderedSplitEdgeBitValue G order b y edge = 1) p
    change ((incCount (kwOrderedSplitEdges G order b y) p : ℕ) : ZMod 2) = _
      at hsum
    rw [hsum]
    simp only [kw_zmod2_indicator_eq]
    have hedgeSum :
        (∑ q ∈ (kwOrderedDartPortSplitGraph G order).neighborFinset p,
          kwOrderedSplitEdgeBitValue G order b y s(p, q)) =
        ∑ q ∈ (kwOrderedDartPortSplitGraph G order).neighborFinset p,
          kwOrderedPortSplitAdjBit G order b y p q := by
      apply Finset.sum_congr rfl
      intro q hq
      let d : (kwOrderedDartPortSplitGraph G order).Dart :=
        ⟨(p, q), (SimpleGraph.mem_neighborFinset _ _ _).mp hq⟩
      exact kwOrderedSplitEdgeBitValue_edge G order b y d
    have hbits :
        (∑ q ∈ (kwOrderedDartPortSplitGraph G order).neighborFinset p,
          kwOrderedPortSplitAdjBit G order b y p q) = 0 := by
      rw [kwOrderedPortSplit_neighbor_sum]
      exact kwOrderedPortSplitIncidence_eq_zero_of_globalEven G order b y hy p
    have hedgeFin :
        (∑ q ∈ (kwOrderedDartPortSplitGraph G order).neighborFinset p,
          kwOrderedSplitEdgeBitValue G order b y s(p, q)) = 0 :=
      hedgeSum.trans hbits
    exact_mod_cast hedgeFin


end StatMech.FrontierA
