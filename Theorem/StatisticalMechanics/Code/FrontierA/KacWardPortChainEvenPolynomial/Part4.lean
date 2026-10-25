/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part32
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStar.Part4
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainEvenPolynomial.Part4
open scoped BigOperators


namespace StatMech.FrontierA

open Finset SimpleGraph

open StatMech.Ising


theorem kw_externalPortBits_sum_eq_neighbor_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : KWDartEdgeBits G) (v : V) :
    (∑ i : Fin (Fintype.card (KWOutgoingDart (G := G) v)),
        kwExternalPortBits G b ⟨v, i⟩) =
      ∑ w ∈ G.neighborFinset v, kwDartEdgeBitValue G b s(v, w) := by
  calc
    (∑ i : Fin (Fintype.card (KWOutgoingDart (G := G) v)),
        kwExternalPortBits G b ⟨v, i⟩) =
        ∑ d : KWOutgoingDart (G := G) v, b.1 d.1 := by
      simpa only [kwExternalPortBits, kwDartOfPort, kwDartPortEquiv,
        Equiv.trans_apply, Equiv.sigmaCongrRight_apply,
        Equiv.sigmaFiberEquiv_apply] using
          (Equiv.sum_comp
            (Fintype.equivFin (KWOutgoingDart (G := G) v)).symm
            (fun d : KWOutgoingDart (G := G) v => b.1 d.1))
    _ = ∑ w : G.neighborSet v,
        b.1 (kwNeighborEquivOutgoingDart G v w).1 := by
      exact (Equiv.sum_comp (kwNeighborEquivOutgoingDart G v)
        (fun d : KWOutgoingDart (G := G) v => b.1 d.1)).symm
    _ = ∑ w : G.neighborSet v, kwDartEdgeBitValue G b s(v, w.1) := by
      apply Finset.sum_congr rfl
      intro w _
      change b.1 ⟨(v, w.1), w.2⟩ = _
      rw [← kwDartEdgeBitValue_edge G b ⟨(v, w.1), w.2⟩]
      rfl
    _ = ∑ w ∈ G.neighborFinset v,
        kwDartEdgeBitValue G b s(v, w) := by
      exact (Finset.sum_subtype (p := fun w => G.Adj v w)
        (G.neighborFinset v)
        (fun w => SimpleGraph.mem_neighborFinset G v w)
        (fun w => kwDartEdgeBitValue G b s(v, w))).symm


theorem kwDartEdgeBitsFinset_even_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : KWDartEdgeBits G) :
    IsEvenSubgraph (kwDartEdgeBitsFinset G b) ↔
      KWOriginalPortEven G b := by
  constructor
  · intro heven v
    rw [kw_externalPortBits_sum_eq_neighbor_sum G b v]
    have hcast : ((incCount (kwDartEdgeBitsFinset G b) v : ℕ) : ZMod 2) = 0 := by
      apply (CharP.cast_eq_zero_iff (ZMod 2) 2 _).mpr
      exact even_iff_two_dvd.mp (heven v)
    have hsum := kw_cast_incCount_filter_eq_neighbor_sum G
      (fun edge => kwDartEdgeBitValue G b edge = 1) v
    change ((incCount (kwDartEdgeBitsFinset G b) v : ℕ) : ZMod 2) = _ at hsum
    rw [hcast] at hsum
    simpa only [kw_zmod2_indicator_eq] using hsum.symm
  · intro hport v
    apply even_iff_two_dvd.mpr
    apply (CharP.cast_eq_zero_iff (ZMod 2) 2 _).mp
    have hneighbor : (∑ w ∈ G.neighborFinset v,
        kwDartEdgeBitValue G b s(v, w)) = 0 := by
      rw [← kw_externalPortBits_sum_eq_neighbor_sum G b v]
      exact hport v
    have hsum := kw_cast_incCount_filter_eq_neighbor_sum G
      (fun edge => kwDartEdgeBitValue G b edge = 1) v
    change ((incCount (kwDartEdgeBitsFinset G b) v : ℕ) : ZMod 2) = _ at hsum
    rw [hsum]
    simpa only [kw_zmod2_indicator_eq] using hneighbor


end StatMech.FrontierA
