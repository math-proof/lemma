/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainEvenPolynomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part32
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStar.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainEvenPolynomial.Part10
open scoped BigOperators


namespace StatMech.FrontierA

open Finset SimpleGraph

open StatMech.Ising


noncomputable def kwOriginalEvenBitsEquivOrderedSplit
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :
    KWOriginalEvenBits G ≃ KWOrderedSplitEvenBits G order where
  toFun b := ⟨⟨b.1, kwOrderedCanonicalPortChainField G order b.1⟩,
    kwOrderedCanonicalPortChainField_even G order b.1 b.2⟩
  invFun p := ⟨p.1.1, by
    apply (kwOrderedDartPortSplit_existsUnique_internal_iff G order p.1.1).mpr
    refine ⟨p.1.2, p.2, ?_⟩
    intro z hz
    exact kwOrderedPortChainField_unique G order p.1.1 z p.1.2 hz p.2⟩
  left_inv b := by
    apply Subtype.ext
    rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (kwOrderedPortChainField_unique G order p.1.1
        (kwOrderedCanonicalPortChainField G order p.1.1) p.1.2
        (kwOrderedCanonicalPortChainField_even G order p.1.1
          ((kwOrderedDartPortSplit_existsUnique_internal_iff G order p.1.1).mpr
            ⟨p.1.2, p.2, fun z hz =>
              kwOrderedPortChainField_unique G order p.1.1 z p.1.2 hz p.2⟩))
        p.2)


noncomputable def kwActualOrderedSplitEvenEquivBits
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :
    KWActualEvenSubgraph (kwOrderedDartPortSplitGraph G order) ≃
      KWOrderedSplitEvenBits G order where
  toFun F := ⟨⟨kwOrderedSplitFinsetExternalBits G F.1,
      kwOrderedSplitFinsetChainField G order F.1⟩,
    kwOrderedSplitFinset_globalEven G order F.1 F.2⟩
  invFun p := ⟨kwOrderedSplitEdges G order p.1.1 p.1.2,
    kwOrderedSplitEdges_even G order p.1.1 p.1.2 p.2⟩
  left_inv F := by
    apply Subtype.ext
    exact kwOrderedSplitEdges_extract G order F.1 F.2
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact kwOrderedSplitFinsetExternalBits_edges G order p.1.1 p.1.2
    · let F := kwOrderedSplitEdges G order p.1.1 p.1.2
      let y' := kwOrderedSplitFinsetChainField G order F
      have hb : kwOrderedSplitFinsetExternalBits G F = p.1.1 :=
        kwOrderedSplitFinsetExternalBits_edges G order p.1.1 p.1.2
      have hy' : KWOrderedGlobalPortChainEven G order p.1.1 y' := by
        rw [← hb]
        exact kwOrderedSplitFinset_globalEven G order F
          (kwOrderedSplitEdges_even G order p.1.1 p.1.2 p.2)
      exact kwOrderedPortChainField_unique G order p.1.1 y' p.1.2 hy' p.2


noncomputable def kwOrderedSplitEvenSubgraphEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :
    KWActualEvenSubgraph G ≃
      KWActualEvenSubgraph (kwOrderedDartPortSplitGraph G order) :=
  (kwActualEvenSubgraphEquivBits G).trans
    ((kwOriginalEvenBitsEquivOrderedSplit G order).trans
      (kwActualOrderedSplitEvenEquivBits G order).symm)


def kwOrderedSplitEdgeProjection
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] :
    Sym2 (KWDartPort G) → Sym2 V :=
  Sym2.map Sigma.fst

end StatMech.FrontierA
