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
import Def.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part18
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


theorem kwOrderedInternalSplitDart_adj_data
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    (d : KWOrderedInternalSplitDart G order) :
    d.1.fst.1 = d.1.snd.1 ∧
      (kwOrderedPortRank order d.1.fst + 1 =
          kwOrderedPortRank order d.1.snd ∨
        kwOrderedPortRank order d.1.snd + 1 =
          kwOrderedPortRank order d.1.fst) := by
  have hd := d.1.adj
  rw [kwOrderedDartPortSplitGraph_adj] at hd
  exact hd.resolve_left d.2


theorem kwOrderedInternalDartStep_rank_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    {d e : KWOrderedInternalSplitDart G order}
    (hstep : KWOrderedInternalDartStep G order d e)
    (hd : kwOrderedPortRank order d.1.fst <
      kwOrderedPortRank order d.1.snd) :
    kwOrderedPortRank order e.1.fst <
      kwOrderedPortRank order e.1.snd := by
  have hddata := kwOrderedInternalSplitDart_adj_data G order d
  have hedata := kwOrderedInternalSplitDart_adj_data G order e
  rcases hddata.2 with hdinc | hddec
  · rcases hedata.2 with heinc | hedec
    · omega
    · exfalso
      apply hstep.2
      rw [SimpleGraph.dart_edge_eq_iff]
      right
      apply SimpleGraph.Dart.ext
      apply Prod.ext
      · change d.1.fst = e.1.snd
        apply kwDartPort_eq_of_fst_of_orderRank order
        · exact hddata.1.trans
            ((congrArg Sigma.fst hstep.1).trans hedata.1)
        · have hrank := congrArg (kwOrderedPortRank order) hstep.1
          omega
      · exact hstep.1
  · omega


theorem kwOrderedInternalDartStep_rank_gt
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    {d e : KWOrderedInternalSplitDart G order}
    (hstep : KWOrderedInternalDartStep G order d e)
    (hd : kwOrderedPortRank order d.1.snd <
      kwOrderedPortRank order d.1.fst) :
    kwOrderedPortRank order e.1.snd <
      kwOrderedPortRank order e.1.fst := by
  have hddata := kwOrderedInternalSplitDart_adj_data G order d
  have hedata := kwOrderedInternalSplitDart_adj_data G order e
  rcases hddata.2 with hdinc | hddec
  · omega
  · rcases hedata.2 with heinc | hedec
    · exfalso
      apply hstep.2
      rw [SimpleGraph.dart_edge_eq_iff]
      right
      apply SimpleGraph.Dart.ext
      apply Prod.ext
      · change d.1.fst = e.1.snd
        apply kwDartPort_eq_of_fst_of_orderRank order
        · exact hddata.1.trans
            ((congrArg Sigma.fst hstep.1).trans hedata.1)
        · have hrank := congrArg (kwOrderedPortRank order) hstep.1
          omega
      · exact hstep.1
    · omega


theorem kwOrderedInternalDartStep_rightUnique
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G)
    {d e f : KWOrderedInternalSplitDart G order}
    (he : KWOrderedInternalDartStep G order d e)
    (hf : KWOrderedInternalDartStep G order d f) : e = f := by
  have hddata := kwOrderedInternalSplitDart_adj_data G order d
  have hedata := kwOrderedInternalSplitDart_adj_data G order e
  have hfdata := kwOrderedInternalSplitDart_adj_data G order f
  apply Subtype.ext
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · exact he.1.symm.trans hf.1
  · apply kwDartPort_eq_of_fst_of_orderRank order
    · exact hedata.1.symm.trans
        ((congrArg Sigma.fst (he.1.symm.trans hf.1)).trans hfdata.1)
    · rcases hddata.2 with hdinc | hddec
      · have hdlt : kwOrderedPortRank order d.1.fst <
            kwOrderedPortRank order d.1.snd := by omega
        have helt := kwOrderedInternalDartStep_rank_lt G order he hdlt
        have hflt := kwOrderedInternalDartStep_rank_lt G order hf hdlt
        have herank := congrArg (kwOrderedPortRank order) he.1
        have hfrank := congrArg (kwOrderedPortRank order) hf.1
        rcases hedata.2 with heinc | hedec <;>
          rcases hfdata.2 with hfinc | hfdec <;> omega
      · have hdgt : kwOrderedPortRank order d.1.snd <
            kwOrderedPortRank order d.1.fst := by omega
        have hegt := kwOrderedInternalDartStep_rank_gt G order he hdgt
        have hfgt := kwOrderedInternalDartStep_rank_gt G order hf hdgt
        have herank := congrArg (kwOrderedPortRank order) he.1
        have hfrank := congrArg (kwOrderedPortRank order) hf.1
        rcases hedata.2 with heinc | hedec <;>
          rcases hfdata.2 with hfinc | hfdec <;> omega


end StatMech.FrontierA
