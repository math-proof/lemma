/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOneVisitInsertedPhase
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredTangentCode
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Instance.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

noncomputable def fkIsingSquareWiredExpandedEmbedding
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)) :
    StatMech.FrontierA.KWStraightLineEmbedding
      (fkIsingSquareWiredExpandedGraph n hn omega) where
  vertex := fkIsingSquareWiredIntPoint ∘
    fkIsingSquareWiredExpandedIntPosition n hn
  vertex_injective := fkIsingSquareWiredIntPoint_injective.comp
    (fkIsingSquareWiredExpandedIntPosition_injective n hn)
  vertex_not_strictly_between := by
    intro dart v _ _
    obtain ⟨a, ha⟩ := fkIsingSquareWiredExpandedGraph_step
      n hn omega dart.adj
    change ¬Sbtw Real
      (fkIsingSquareWiredIntPoint
        (fkIsingSquareWiredExpandedIntPosition n hn dart.fst))
      (fkIsingSquareWiredIntPoint
        (fkIsingSquareWiredExpandedIntPosition n hn v))
      (fkIsingSquareWiredIntPoint
        (fkIsingSquareWiredExpandedIntPosition n hn dart.snd))
    rw [ha]
    exact fkIsingSquareWiredIntPoint_not_strictly_between_unitDiagonal
      (fkIsingSquareWiredExpandedIntPosition n hn dart.fst)
      (fkIsingSquareWiredExpandedIntPosition n hn v) a
  edgeInteriors_disjoint := by
    intro dart next hedge
    apply Set.disjoint_left.2
    intro z hzd hzn
    apply hedge
    apply fkIsingSquareWiredExpandedGraph_edge_eq_of_midpoint_eq
      n hn omega dart.adj next.adj
    obtain ⟨a, ha⟩ := fkIsingSquareWiredExpandedGraph_step
      n hn omega dart.adj
    obtain ⟨b, hb⟩ := fkIsingSquareWiredExpandedGraph_step
      n hn omega next.adj
    change
      fkIsingSquareWiredExpandedIntPosition n hn dart.fst +
          fkIsingSquareWiredExpandedIntPosition n hn dart.snd =
        fkIsingSquareWiredExpandedIntPosition n hn next.fst +
          fkIsingSquareWiredExpandedIntPosition n hn next.snd
    rw [ha, hb]
    exact fkIsingSquareWiredUnitDiagonal_open_intersection_midpoint_eq
      (fkIsingSquareWiredExpandedIntPosition n hn dart.fst)
      (fkIsingSquareWiredExpandedIntPosition n hn next.fst)
      a b z (by simpa [ha] using hzd) (by simpa [hb] using hzn)


end
end StatMech.Universality
