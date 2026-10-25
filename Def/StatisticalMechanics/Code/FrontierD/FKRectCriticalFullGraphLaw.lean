/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCriticalFullGraphLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterFKG.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part9
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigEventLaw.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCriticalFullGraphLaw
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech

def fkRectFullEdgeConfigEquiv (R : FKRectTorus) :
    R.Configuration ≃ FK.ecz_ClosedOff (fkRectTorusGraph R) where
  toFun omega := ⟨fkRectFullGraphConfiguration R omega, by
    intro e he
    apply fkRectFullGraphConfiguration_eq_false_of_not_edge R omega
    simpa only [SimpleGraph.mem_edgeFinset] using he⟩
  invFun sigma a := sigma.1 (fkRectTorusIndexedEdge R a)
  left_inv omega := by
    funext a
    exact fkRectFullGraphConfiguration_indexedEdge R omega a
  right_inv sigma := by
    apply Subtype.ext
    funext e
    change fkRectFullGraphConfiguration R
        (fun a => sigma.1 (fkRectTorusIndexedEdge R a)) e = sigma.1 e
    by_cases he : e ∈ (fkRectTorusGraph R).edgeSet
    · obtain ⟨a, ha⟩ := (mem_fkRectTorusGraph_edgeSet_iff R e).1 he
      rw [← ha, fkRectFullGraphConfiguration_indexedEdge]
    · rw [fkRectFullGraphConfiguration_eq_false_of_not_edge R _ he]
      symm
      apply sigma.2 e
      simpa only [SimpleGraph.mem_edgeFinset] using he


def fkRectFullEdgeEvent (R : FKRectTorus) (A : Set R.Configuration) :
    Set (FK.ecz_ClosedOff (fkRectTorusGraph R)) :=
  {sigma | (fkRectFullEdgeConfigEquiv R).symm sigma ∈ A}


end
end StatMech.FrontierD
