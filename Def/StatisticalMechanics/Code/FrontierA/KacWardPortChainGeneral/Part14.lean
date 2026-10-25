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
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainGeneral.Part13
open scoped BigOperators


namespace StatMech.FrontierA

open SimpleGraph Finset


noncomputable def kwOrderedInternalSplitDartEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (order : KWPortOrder G) :
    KWOrderedInternalSplitDart G order ≃
      (kwOrderedPortInternalGraph G order).Dart where
  toFun delta := by
    refine ⟨delta.1.toProd, ?_⟩
    have hadj := delta.1.adj
    rw [kwOrderedDartPortSplitGraph_adj] at hadj
    exact hadj.resolve_left delta.2
  invFun delta := by
    have hfull : (kwOrderedDartPortSplitGraph G order).Adj
        delta.fst delta.snd := by
      rw [kwOrderedDartPortSplitGraph_adj]
      exact Or.inr delta.adj
    have hnot : ¬kwDartOfPort G delta.snd =
        (kwDartOfPort G delta.fst).symm := by
      intro hext
      have htails := congrArg (fun d : G.Dart ↦ d.fst) hext
      have hsame : delta.fst.1 = delta.snd.1 := delta.adj.1
      apply (kwDartOfPort G delta.fst).fst_ne_snd
      rw [kwDartOfPort_fst, hsame]
      simpa using htails
    exact ⟨⟨delta.toProd, hfull⟩, hnot⟩
  left_inv delta := by
    apply Subtype.ext
    apply SimpleGraph.Dart.ext
    rfl
  right_inv delta := by
    apply SimpleGraph.Dart.ext
    rfl

end StatMech.FrontierA
