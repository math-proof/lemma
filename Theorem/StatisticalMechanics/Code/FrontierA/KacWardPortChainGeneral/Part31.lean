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
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part33
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


theorem kwCanonicalPortChainField_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : KWDartEdgeBits G)
    (hb : KWOriginalPortEven G b) :
    KWGlobalPortChainEven G b (kwCanonicalPortChainField G b) := by
  intro v
  exact ⟨kwPortChainState_zero _, kwPortChainState_succ _,
    (kwPortChainState_last_eq_zero_iff _).2 (hb v)⟩

theorem kwPortChainField_eq_canonical
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : KWDartEdgeBits G)
    (y : KWPortChainField G) (hy : KWGlobalPortChainEven G b y) :
    y = kwCanonicalPortChainField G b := by
  funext v
  exact kwPortChainState_unique _ (y v) (hy v).1 (hy v).2.1

theorem kwOriginalPortEven_of_globalPortChainEven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : KWDartEdgeBits G)
    (y : KWPortChainField G) (hy : KWGlobalPortChainEven G b y) :
    KWOriginalPortEven G b := by
  intro v
  have hsum := kwPortChain_sum_eq_endpoints
    (fun i ↦ kwExternalPortBits G b ⟨v, i⟩) (y v) (hy v).2.1
  rw [(hy v).1, (hy v).2.2, add_zero] at hsum
  exact hsum


end StatMech.FrontierA
