/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part32
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStar.Part4
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainEvenPolynomial.Part12
open scoped BigOperators


namespace StatMech.FrontierA

open Finset SimpleGraph

open StatMech.Ising


@[simp] theorem kwOrderedSplitEdgeProjection_mk
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (p q : KWDartPort G) :
    kwOrderedSplitEdgeProjection s(p, q) = s(p.1, q.1) := by
  simp [kwOrderedSplitEdgeProjection]

theorem kwOrderedSplit_external_of_projection_not_diag
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    {p q : KWDartPort G}
    (hpq : (kwOrderedDartPortSplitGraph G order).Adj p q)
    (hdiag : ¬(kwOrderedSplitEdgeProjection s(p, q)).IsDiag) :
    kwDartOfPort G q = (kwDartOfPort G p).symm := by
  rw [kwOrderedDartPortSplitGraph_adj] at hpq
  rcases hpq with hext | hint
  · exact hext
  · exfalso
    apply hdiag
    rw [kwOrderedSplitEdgeProjection_mk, Sym2.mk_isDiag_iff]
    exact hint.1

theorem kwDartOfPort_toProd_of_external
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {p q : KWDartPort G}
    (hext : kwDartOfPort G q = (kwDartOfPort G p).symm) :
    (kwDartOfPort G p).toProd = (p.1, q.1) := by
  apply Prod.ext
  · exact kwDartOfPort_fst G p
  · have hfirst := congrArg (fun d : G.Dart => d.fst) hext
    change (kwDartOfPort G q).fst = (kwDartOfPort G p).snd at hfirst
    rw [kwDartOfPort_fst] at hfirst
    exact hfirst.symm

theorem kwOrderedSplitEdgeProjection_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    {edge edge' : Sym2 (KWDartPort G)}
    (hedge : edge ∈ (kwOrderedDartPortSplitGraph G order).edgeFinset)
    (hedge' : edge' ∈ (kwOrderedDartPortSplitGraph G order).edgeFinset)
    (hdiag : ¬(kwOrderedSplitEdgeProjection edge).IsDiag)
    (hdiag' : ¬(kwOrderedSplitEdgeProjection edge').IsDiag)
    (heq : kwOrderedSplitEdgeProjection edge =
      kwOrderedSplitEdgeProjection edge') : edge = edge' := by
  induction edge using Sym2.inductionOn with
  | _ p q =>
    induction edge' using Sym2.inductionOn with
    | _ r s =>
      have hpq : (kwOrderedDartPortSplitGraph G order).Adj p q :=
        SimpleGraph.mem_edgeFinset.mp hedge
      have hrs : (kwOrderedDartPortSplitGraph G order).Adj r s :=
        SimpleGraph.mem_edgeFinset.mp hedge'
      have hpqext := kwOrderedSplit_external_of_projection_not_diag
        G order hpq hdiag
      have hrsext := kwOrderedSplit_external_of_projection_not_diag
        G order hrs hdiag'
      rw [kwOrderedSplitEdgeProjection_mk,
        kwOrderedSplitEdgeProjection_mk, Sym2.eq_iff] at heq
      rcases heq with heq | heq
      · have hpr : p = r := by
          apply kwDartOfPort_injective G
          apply SimpleGraph.Dart.ext
          rw [kwDartOfPort_toProd_of_external G hpqext,
            kwDartOfPort_toProd_of_external G hrsext, heq.1, heq.2]
        have hqs : q = s := by
          apply kwDartOfPort_injective G
          rw [hpqext, hrsext, hpr]
        rw [hpr, hqs]
      · have hps : p = s := by
          apply kwDartOfPort_injective G
          apply SimpleGraph.Dart.ext
          rw [kwDartOfPort_toProd_of_external G hpqext]
          have hsrev : kwDartOfPort G r = (kwDartOfPort G s).symm := by
            rw [hrsext]
            exact (kwDartOfPort G r).symm_symm.symm
          rw [kwDartOfPort_toProd_of_external G hsrev, heq.1, heq.2]
        have hqr : q = r := by
          apply kwDartOfPort_injective G
          calc
            kwDartOfPort G q = (kwDartOfPort G p).symm := hpqext
            _ = (kwDartOfPort G s).symm := by rw [hps]
            _ = ((kwDartOfPort G r).symm).symm := by rw [hrsext]
            _ = kwDartOfPort G r := (kwDartOfPort G r).symm_symm
        rw [hps, hqr]
        exact Sym2.eq_swap

theorem kwOrderedSplitWeight_eq_one_of_projection_diag
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (weight : Sym2 V → ℂ)
    {edge : Sym2 (KWDartPort G)} (hdiag :
      (kwOrderedSplitEdgeProjection edge).IsDiag) :
    kwOrderedSplitWeight G weight edge = 1 := by
  induction edge using Sym2.inductionOn with
  | _ p q =>
    rw [kwOrderedSplitEdgeProjection_mk, Sym2.mk_isDiag_iff] at hdiag
    unfold kwOrderedSplitWeight
    change (if kwDartOfPort G q = (kwDartOfPort G p).symm
      then weight (kwDartOfPort G p).edge else 1) = 1
    by_cases hext : kwDartOfPort G q = (kwDartOfPort G p).symm
    · have hfirst := congrArg (fun d : G.Dart => d.fst) hext
      change (kwDartOfPort G q).fst = (kwDartOfPort G p).snd at hfirst
      rw [kwDartOfPort_fst] at hfirst
      exact ((kwDartOfPort G p).fst_ne_snd (by
        calc
          (kwDartOfPort G p).fst = p.1 := kwDartOfPort_fst G p
          _ = q.1 := hdiag
          _ = (kwDartOfPort G p).snd := hfirst)).elim
    · rw [if_neg hext]

theorem kwOrderedSplitWeight_eq_projection_of_not_diag
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (weight : Sym2 V → ℂ) {edge : Sym2 (KWDartPort G)}
    (hedge : edge ∈ (kwOrderedDartPortSplitGraph G order).edgeFinset)
    (hdiag : ¬(kwOrderedSplitEdgeProjection edge).IsDiag) :
    kwOrderedSplitWeight G weight edge =
      weight (kwOrderedSplitEdgeProjection edge) := by
  induction edge using Sym2.inductionOn with
  | _ p q =>
    have hpq : (kwOrderedDartPortSplitGraph G order).Adj p q :=
      SimpleGraph.mem_edgeFinset.mp hedge
    have hext := kwOrderedSplit_external_of_projection_not_diag
      G order hpq hdiag
    unfold kwOrderedSplitWeight
    change (if kwDartOfPort G q = (kwDartOfPort G p).symm
      then weight (kwDartOfPort G p).edge else 1) =
        weight (kwOrderedSplitEdgeProjection s(p, q))
    rw [if_pos hext, kwOrderedSplitEdgeProjection_mk]
    have hprod := kwDartOfPort_toProd_of_external G hext
    unfold SimpleGraph.Dart.edge
    rw [hprod]


theorem kwOrderedSplitEdges_weight_prod
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (weight : Sym2 V → ℂ) (b : KWDartEdgeBits G)
    (y : KWPortChainField G) :
    (∏ edge ∈ kwOrderedSplitEdges G order b y,
        kwOrderedSplitWeight G weight edge) =
      ∏ edge ∈ kwDartEdgeBitsFinset G b, weight edge := by
  classical
  let S := (kwOrderedSplitEdges G order b y).filter fun edge =>
    ¬(kwOrderedSplitEdgeProjection edge).IsDiag
  let T := kwDartEdgeBitsFinset G b
  have hremove :
      (∏ edge ∈ S, kwOrderedSplitWeight G weight edge) =
        ∏ edge ∈ kwOrderedSplitEdges G order b y,
          kwOrderedSplitWeight G weight edge := by
    apply Finset.prod_subset (Finset.filter_subset _ _)
    intro edge hedge hnot
    apply kwOrderedSplitWeight_eq_one_of_projection_diag G weight
    by_contra hdiag
    apply hnot
    exact Finset.mem_filter.mpr ⟨hedge, hdiag⟩
  rw [← hremove]
  apply Finset.prod_bij
    (fun edge (_ : edge ∈ S) => kwOrderedSplitEdgeProjection edge)
  · intro edge hedge
    have hdata := Finset.mem_filter.mp hedge
    induction edge using Sym2.inductionOn with
    | _ p q =>
      have hpqEdge : s(p, q) ∈
          (kwOrderedDartPortSplitGraph G order).edgeFinset :=
        (Finset.filter_subset _ _) hdata.1
      have hpq : (kwOrderedDartPortSplitGraph G order).Adj p q :=
        SimpleGraph.mem_edgeFinset.mp hpqEdge
      have hext := kwOrderedSplit_external_of_projection_not_diag
        G order hpq hdata.2
      let d : (kwOrderedDartPortSplitGraph G order).Dart := ⟨(p, q), hpq⟩
      have hbit : kwOrderedPortSplitAdjBit G order b y p q = 1 :=
        (mem_kwOrderedSplitEdges_iff G order b y d).mp hdata.1
      unfold kwOrderedPortSplitAdjBit at hbit
      rw [if_pos hext] at hbit
      have hproj : kwOrderedSplitEdgeProjection s(p, q) =
          (kwDartOfPort G p).edge := by
        rw [kwOrderedSplitEdgeProjection_mk]
        have hprod := kwDartOfPort_toProd_of_external G hext
        unfold SimpleGraph.Dart.edge
        rw [hprod]
      rw [hproj]
      exact (mem_kwDartEdgeBitsFinset_iff G b (kwDartOfPort G p)).mpr hbit
  · intro edge hedge edge' hedge' heq
    have hdata := Finset.mem_filter.mp hedge
    have hdata' := Finset.mem_filter.mp hedge'
    exact kwOrderedSplitEdgeProjection_injective G order
      ((Finset.filter_subset _ _) hdata.1)
      ((Finset.filter_subset _ _) hdata'.1) hdata.2 hdata'.2 heq
  · intro edge hedge
    induction edge using Sym2.inductionOn with
    | _ v w =>
      have hdata := Finset.mem_filter.mp hedge
      have hvw : G.Adj v w := by simpa using hdata.1
      let d : G.Dart := ⟨(v, w), hvw⟩
      let delta := (kwOrderedExternalSplitDartOfDart G order d).1
      have hproj : kwOrderedSplitEdgeProjection delta.edge = d.edge := by
        have hp : (kwPortOfDart G d).1 = d.fst := by
          simpa using (kwDartOfPort_fst G (kwPortOfDart G d)).symm
        have hq : (kwPortOfDart G d.symm).1 = d.snd := by
          simpa using (kwDartOfPort_fst G (kwPortOfDart G d.symm)).symm
        change s((kwPortOfDart G d).1,
          (kwPortOfDart G d.symm).1) = d.edge
        rw [hp, hq]
        rfl
      refine ⟨delta.edge, ?_, ?_⟩
      · rw [Finset.mem_filter]
        constructor
        · apply (mem_kwOrderedSplitEdges_iff G order b y delta).mpr
          have hmatch : delta.snd = kwOrderedMatchingNeighbor G delta.fst := by
            apply kwDartOfPort_injective G
            simp [delta, kwOrderedMatchingNeighbor]
          rw [hmatch, kwOrderedPortSplitAdjBit_matching]
          have hb : b.1 d = 1 := by
            have hdedge : d.edge = s(v, w) := rfl
            rw [← hdedge, kwDartEdgeBitValue_edge] at hdata
            exact hdata.2
          simpa [delta, kwExternalPortBits, d] using hb
        · rw [hproj]
          simpa [d, SimpleGraph.Dart.edge, Sym2.mk_isDiag_iff] using hvw.ne
      · simpa [d, SimpleGraph.Dart.edge] using hproj
  · intro edge hedge
    have hdata := Finset.mem_filter.mp hedge
    apply kwOrderedSplitWeight_eq_projection_of_not_diag G order weight
    · exact (Finset.filter_subset _ _) hdata.1
    · exact hdata.2

theorem kwEvenPolynomial_eq_sum_actual
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) :
    kwEvenPolynomial G weight =
      ∑ F : KWActualEvenSubgraph G, ∏ edge ∈ F.1, weight edge := by
  unfold kwEvenPolynomial KWActualEvenSubgraph
  exact Finset.sum_subtype (G.edgeFinset.powerset.filter IsEvenSubgraph)
    (fun F => Iff.rfl) (fun F => ∏ edge ∈ F, weight edge)


theorem kwOrderedSplit_evenPolynomial_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (weight : Sym2 V → ℂ) :
    kwEvenPolynomial (kwOrderedDartPortSplitGraph G order)
        (kwOrderedSplitWeight G weight) =
      kwEvenPolynomial G weight := by
  rw [kwEvenPolynomial_eq_sum_actual, kwEvenPolynomial_eq_sum_actual]
  symm
  apply Fintype.sum_equiv (kwOrderedSplitEvenSubgraphEquiv G order)
  intro F
  have hdata := F.2
  change F.1 ∈ G.edgeFinset.powerset.filter IsEvenSubgraph at hdata
  rw [Finset.mem_filter, Finset.mem_powerset] at hdata
  let b := kwFinsetDartEdgeBits G F.1
  let y := kwOrderedCanonicalPortChainField G order b
  have hprod := kwOrderedSplitEdges_weight_prod G order weight b y
  have hFset : kwDartEdgeBitsFinset G b = F.1 :=
    kwDartEdgeBitsFinset_finset G F.1 hdata.1
  rw [hFset] at hprod
  simpa [kwOrderedSplitEvenSubgraphEquiv,
    kwActualEvenSubgraphEquivBits, kwOriginalEvenBitsEquivOrderedSplit,
    kwActualOrderedSplitEvenEquivBits, Equiv.trans_apply, b, y] using hprod.symm

end StatMech.FrontierA
