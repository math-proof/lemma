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
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part25
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


def KWOriginalPortEven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : KWDartEdgeBits G) : Prop :=
  ∀ v, (∑ i : Fin (Fintype.card (KWOutgoingDart (G := G) v)),
    kwExternalPortBits G b ⟨v, i⟩) = 0


def KWPortChainField
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :=
  (v : V) → Fin (Fintype.card (KWOutgoingDart (G := G) v) + 1) → Fin 2

end StatMech.FrontierA
