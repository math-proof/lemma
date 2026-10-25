/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalFullSquareGhost.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFiniteGhostComparison.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRangeTransfer
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredFullFaces.Part9
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareGhost.Part3
open SimpleGraph


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

def fkIsingSquareRadialPatchPrimalFullVertex
    (n m : Nat) (hm : m ≤ n) :
    FKIsingSquareRadialPatchPrimalNode m → FKIsingSquareFullVertexNode n :=
  fkIsingSquareRadialPatchPrimalNodeVertex n m hm


def fkIsingSquareRadialPatchDualFullFace
    (n m : Nat) (hm : m ≤ n) (hm2 : 2 ≤ m)
    (q : FKIsingSquareRadialPatchDualNode m) :
    FKIsingSquareFullFaceNode n := by
  let half := (q.1.1.1 + q.1.2.1 + 1) / 2
  have hmod := Nat.not_even_iff.mp q.2
  have hn : 0 < n := by omega
  refine (⟨n + half - 1, by
      have hi := q.1.1.2
      have hj := q.1.2.2
      omega⟩,
    ⟨n + q.1.1.1 - half, by
      have hi := q.1.1.2
      have hj := q.1.2.2
      omega⟩)

end
end StatMech.Universality
