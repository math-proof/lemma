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
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part30
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


theorem kwOrderedPortSplitIncidence_eq_zero_of_globalEven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : KWPortOrder G) (b : KWDartEdgeBits G)
    (y : KWPortChainField G)
    (hy : KWOrderedGlobalPortChainEven G order b y) (p : KWDartPort G) :
    kwOrderedPortSplitIncidence G order b y p = 0 := by
  let i := order p.1 p.2
  have hp := hy p.1
  have hbit : kwExternalPortBits G b p =
      kwExternalPortBits G b (kwPortAtOrderedRank order p.1 i) := by
    have heq : kwPortAtOrderedRank order p.1 i = p := by
      rcases p with ⟨v, j⟩
      simp [kwPortAtOrderedRank, i]
    rw [heq]
  have hleft :
      (if kwOrderedPortRank order p = 0 then 0
        else y p.1 i.castSucc) = y p.1 i.castSucc := by
    by_cases hzero : kwOrderedPortRank order p = 0
    · rw [if_pos hzero]
      symm
      rw [← hp.1]
      congr 1
      apply Fin.ext
      exact hzero
    · rw [if_neg hzero]
  have hright :
      (if kwOrderedPortRank order p + 1 =
          Fintype.card (KWOutgoingDart (G := G) p.1) then 0
        else y p.1 i.succ) = y p.1 i.succ := by
    by_cases hlast : kwOrderedPortRank order p + 1 =
        Fintype.card (KWOutgoingDart (G := G) p.1)
    · rw [if_pos hlast]
      symm
      rw [← hp.2.2]
      congr 1
      apply Fin.ext
      exact hlast
    · rw [if_neg hlast]
  unfold kwOrderedPortSplitIncidence
  rw [hbit, hleft, hright, hp.2.1 i]
  calc
    kwExternalPortBits G b (kwPortAtOrderedRank order p.1 i) +
        y p.1 i.castSucc +
        (y p.1 i.castSucc +
          kwExternalPortBits G b (kwPortAtOrderedRank order p.1 i)) =
      (kwExternalPortBits G b (kwPortAtOrderedRank order p.1 i) +
          kwExternalPortBits G b (kwPortAtOrderedRank order p.1 i)) +
        (y p.1 i.castSucc + y p.1 i.castSucc) := by ac_rfl
    _ = 0 := by rw [kw_fin_two_self_add, kw_fin_two_self_add, add_zero]


end StatMech.FrontierA
