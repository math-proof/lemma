/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part32
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStar.Part4
import Instance.StatisticalMechanics.Code.FrontierA.KacWardPortChainEvenPolynomial
open scoped BigOperators


namespace StatMech.FrontierA

open Finset SimpleGraph

open StatMech.Ising


noncomputable def kwActualEvenSubgraphEquivBits
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    KWActualEvenSubgraph G ≃ KWOriginalEvenBits G where
  toFun F := ⟨kwFinsetDartEdgeBits G F.1, by
    have hdata := F.2
    change F.1 ∈ G.edgeFinset.powerset.filter IsEvenSubgraph at hdata
    rw [Finset.mem_filter, Finset.mem_powerset] at hdata
    apply (kwDartEdgeBitsFinset_even_iff G _).mp
    rw [kwDartEdgeBitsFinset_finset G F.1 hdata.1]
    exact hdata.2⟩
  invFun b := ⟨kwDartEdgeBitsFinset G b.1, by
    rw [evenSubgraphs, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.filter_subset _ _,
      (kwDartEdgeBitsFinset_even_iff G b.1).mpr b.2⟩⟩
  left_inv F := by
    apply Subtype.ext
    have hdata := F.2
    change F.1 ∈ G.edgeFinset.powerset.filter IsEvenSubgraph at hdata
    rw [Finset.mem_filter, Finset.mem_powerset] at hdata
    exact kwDartEdgeBitsFinset_finset G F.1 hdata.1
  right_inv b := by
    apply Subtype.ext
    exact kwFinsetDartEdgeBits_bitsFinset G b.1


def KWOrderedSplitEvenBits
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :=
  {p : KWDartEdgeBits G × KWPortChainField G //
    KWOrderedGlobalPortChainEven G order p.1 p.2}

noncomputable def kwOrderedCanonicalPortChainField
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (b : KWDartEdgeBits G) : KWPortChainField G :=
  fun v => kwPortChainState
    (fun i => kwExternalPortBits G b (kwPortAtOrderedRank order v i))

end StatMech.FrontierA
