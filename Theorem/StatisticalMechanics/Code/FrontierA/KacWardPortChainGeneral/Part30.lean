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
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part32
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


theorem kwPortSplitIncidence_eq_zero_of_globalEven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (b : KWDartEdgeBits G) (y : KWPortChainField G)
    (hy : KWGlobalPortChainEven G b y) (p : KWDartPort G) :
    kwPortSplitIncidence G b y p = 0 := by
  let n := Fintype.card (KWOutgoingDart (G := G) p.1)
  let bit : Fin n → Fin 2 := fun i ↦ kwExternalPortBits G b ⟨p.1, i⟩
  have hp := hy p.1
  have hleft :
      (if p.2.val = 0 then 0 else y p.1 p.2.castSucc) =
        y p.1 p.2.castSucc := by
    by_cases hzero : p.2.val = 0
    · rw [if_pos hzero]
      symm
      rw [← hp.1]
      congr 1
      apply Fin.ext
      simpa using hzero
    · rw [if_neg hzero]
  have hright :
      (if p.2.val + 1 = n then 0 else y p.1 p.2.succ) =
        y p.1 p.2.succ := by
    by_cases hlast : p.2.val + 1 = n
    · rw [if_pos hlast]
      symm
      rw [← hp.2.2]
      congr 1
      apply Fin.ext
      simpa [n] using hlast
    · rw [if_neg hlast]
  change bit p.2 +
      (if p.2.val = 0 then 0 else y p.1 p.2.castSucc) +
      (if p.2.val + 1 = n then 0 else y p.1 p.2.succ) = 0
  rw [hleft, hright, hp.2.1 p.2]
  calc
    bit p.2 + y p.1 p.2.castSucc +
        (y p.1 p.2.castSucc + bit p.2) =
      (bit p.2 + bit p.2) +
        (y p.1 p.2.castSucc + y p.1 p.2.castSucc) := by ac_rfl
    _ = 0 := by rw [kw_fin_two_self_add, kw_fin_two_self_add, add_zero]


theorem kwDartPortSplit_existsUnique_internal_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (b : KWDartEdgeBits G) :
    KWOriginalPortEven G b ↔ ∃! y : KWPortChainField G,
      KWGlobalPortChainEven G b y := by
  constructor
  · intro hb
    let y : KWPortChainField G := fun v ↦
      kwPortChainState (fun i ↦ kwExternalPortBits G b ⟨v, i⟩)
    refine ⟨y, ?_, ?_⟩
    · intro v
      exact ⟨kwPortChainState_zero _, kwPortChainState_succ _,
        (kwPortChainState_last_eq_zero_iff _).2 (hb v)⟩
    · intro z hz
      funext v
      exact kwPortChainState_unique _ (z v) (hz v).1 (hz v).2.1
  · rintro ⟨y, hy, -⟩
    intro v
    have hsum := kwPortChain_sum_eq_endpoints
      (fun i ↦ kwExternalPortBits G b ⟨v, i⟩) (y v) (hy v).2.1
    rw [(hy v).1, (hy v).2.2, add_zero] at hsum
    exact hsum


end StatMech.FrontierA
