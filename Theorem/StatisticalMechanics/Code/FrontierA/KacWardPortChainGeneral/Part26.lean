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
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part28
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


theorem kwOrderedExternalPortBits_sum_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (b : KWDartEdgeBits G) (v : V) :
    (∑ i, kwExternalPortBits G b (kwPortAtOrderedRank order v i)) =
      ∑ i, kwExternalPortBits G b ⟨v, i⟩ := by
  exact Equiv.sum_comp (order v).symm
    (fun i ↦ kwExternalPortBits G b ⟨v, i⟩)


theorem kwOrderedDartPortSplit_existsUnique_internal_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (b : KWDartEdgeBits G) :
    KWOriginalPortEven G b ↔ ∃! y : KWPortChainField G,
      KWOrderedGlobalPortChainEven G order b y := by
  constructor
  · intro hb
    let y : KWPortChainField G := fun v ↦ kwPortChainState
      (fun i ↦ kwExternalPortBits G b (kwPortAtOrderedRank order v i))
    refine ⟨y, ?_, ?_⟩
    · intro v
      refine ⟨kwPortChainState_zero _, kwPortChainState_succ _, ?_⟩
      apply (kwPortChainState_last_eq_zero_iff _).2
      rw [kwOrderedExternalPortBits_sum_eq G order b v, hb v]
    · intro z hz
      funext v
      exact kwPortChainState_unique _ (z v) (hz v).1 (hz v).2.1
  · rintro ⟨y, hy, -⟩
    intro v
    have hsum := kwPortChain_sum_eq_endpoints
      (fun i ↦ kwExternalPortBits G b (kwPortAtOrderedRank order v i))
      (y v) (hy v).2.1
    rw [(hy v).1, (hy v).2.2, add_zero] at hsum
    rw [← kwOrderedExternalPortBits_sum_eq G order b v]
    exact hsum


end StatMech.FrontierA
