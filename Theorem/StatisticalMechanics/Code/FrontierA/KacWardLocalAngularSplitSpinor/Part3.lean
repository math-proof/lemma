/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardLocalAngularSplitSpinor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardLocalAngularSplit.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularSplitSpinor.Part3
import Def.StatisticalMechanics.Code.FrontierA.KacWardLocalAngularSplitSpinor.Part2


namespace StatMech.FrontierA

open SimpleGraph

open scoped BigOperators


theorem kwLocalAngularSplitSpinorDirection_symm
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    (d : (kwOrderedDartPortSplitGraph G
      (data.order)).Dart) :
    kwLocalAngularSplitSpinorDirection data d.symm =
      -kwLocalAngularSplitSpinorDirection data d := by
  classical
  have hmatchingRev :
      kwDartOfPort G d.symm.snd =
          (kwDartOfPort G d.symm.fst).symm ↔
        kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm := by
    change kwDartOfPort G d.fst = (kwDartOfPort G d.snd).symm ↔
      kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm
    constructor
    · intro h
      rw [h]
      simp
    · intro h
      rw [h]
      simp
  by_cases hmatching :
      kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm
  · have hmatching' :
        kwDartOfPort G d.symm.snd =
          (kwDartOfPort G d.symm.fst).symm := hmatchingRev.mpr hmatching
    unfold kwLocalAngularSplitSpinorDirection
    rw [if_pos hmatching', if_pos hmatching]
    change data.root d.snd ^ 2 =
      -(data.root d.fst ^ 2)
    exact kwLocalPortRoot_sq_of_matching data hmatching
  · have hmatching' :
        ¬kwDartOfPort G d.symm.snd =
          (kwDartOfPort G d.symm.fst).symm := by
        simpa only [hmatchingRev] using hmatching
    have hadj := d.adj
    rw [kwOrderedDartPortSplitGraph_adj] at hadj
    have hinternal := hadj.resolve_left hmatching
    have hmatchingSwap :
        ¬kwDartOfPort G d.fst = (kwDartOfPort G d.snd).symm := by
      intro h
      apply hmatching
      rw [h]
      simp
    rcases hinternal.2 with hinc | hdec
    · have hlt : kwOrderedPortRank (data.order) d.fst <
          kwOrderedPortRank (data.order) d.snd := by omega
      have hnrev : ¬kwOrderedPortRank (data.order) d.snd <
          kwOrderedPortRank (data.order) d.fst := by omega
      unfold kwLocalAngularSplitSpinorDirection
      change (if kwDartOfPort G d.fst = (kwDartOfPort G d.snd).symm then _
          else if kwOrderedPortRank (data.order) d.snd <
            kwOrderedPortRank (data.order) d.fst then -1 else 1) =
        -(if kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm then _
          else if kwOrderedPortRank (data.order) d.fst <
            kwOrderedPortRank (data.order) d.snd then -1 else 1)
      rw [if_neg hmatchingSwap, if_neg hmatching,
        if_neg hnrev, if_pos hlt]
      norm_num
    · have hnlt : ¬kwOrderedPortRank (data.order) d.fst <
          kwOrderedPortRank (data.order) d.snd := by omega
      have hrev : kwOrderedPortRank (data.order) d.snd <
          kwOrderedPortRank (data.order) d.fst := by omega
      unfold kwLocalAngularSplitSpinorDirection
      change (if kwDartOfPort G d.fst = (kwDartOfPort G d.snd).symm then _
          else if kwOrderedPortRank (data.order) d.snd <
            kwOrderedPortRank (data.order) d.fst then -1 else 1) =
        -(if kwDartOfPort G d.snd = (kwDartOfPort G d.fst).symm then _
          else if kwOrderedPortRank (data.order) d.fst <
            kwOrderedPortRank (data.order) d.snd then -1 else 1)
      rw [if_neg hmatchingSwap, if_neg hmatching,
        if_pos hrev, if_neg hnlt]


end StatMech.FrontierA
