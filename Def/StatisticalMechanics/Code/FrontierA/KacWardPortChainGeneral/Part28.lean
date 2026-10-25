/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardPortChainGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAcyclicElimination.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardStraightLineEmbedding.Part2
import Mathlib.Data.Finset.Sort
import Instance.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part7
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


def KWGlobalPortChainEven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : KWDartEdgeBits G) (y : KWPortChainField G) : Prop :=
  ∀ v, KWPortChainEven
    (fun i ↦ kwExternalPortBits G b ⟨v, i⟩) (y v)


def kwPortAtOrderedRank
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (order : KWPortOrder G) (v : V)
    (i : Fin (Fintype.card (KWOutgoingDart (G := G) v))) : KWDartPort G :=
  ⟨v, (order v).symm i⟩


def KWOrderedGlobalPortChainEven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (b : KWDartEdgeBits G)
    (y : KWPortChainField G) : Prop :=
  ∀ v, KWPortChainEven
    (fun i ↦ kwExternalPortBits G b (kwPortAtOrderedRank order v i))
    (y v)

end StatMech.FrontierA
