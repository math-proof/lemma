/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedSquare.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutSquareEmbedding.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterGraphBridge.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquarePeriodicDualCoordinates
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCriticalDualQuasiInvariant.Part2
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossingCover.Part7
import Def.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquare.Part3
open StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

theorem fkRectDevelopedSquarePullback_mono
    (R : FKRectTorus) (n : Nat) {omega tau : R.Configuration}
    (hot : omega ≤ tau) :
    fkRectDevelopedSquarePullback R n omega ≤
      fkRectDevelopedSquarePullback R n tau := by
  intro e
  unfold fkRectDevelopedSquarePullback fkRectFullGraphConfiguration
  split
  · exact hot _
  · rfl


theorem fkRectDevelopedSquarePullback_open_iff
    (R : FKRectTorus) (n : Nat)
    (hwidth : 3 * n < R.width) (hheight : 3 * n < R.height)
    (omega : R.Configuration) {z w : Site 2}
    (hz : z ∈ StatMech.RSW.Box.rect 0 n 0 n)
    (hw : w ∈ StatMech.RSW.Box.rect 0 n 0 n)
    (hzw : (hypercubicLattice 2).Adj z w) :
    fkRectDevelopedSquarePullback R n omega s(z, w) = true ↔
      (fkRectOpenGraph R omega).Adj
        (fkRectDevelopedSquareVertex R n z)
        (fkRectDevelopedSquareVertex R n w) := by
  have hcut := fkRectDevelopedSquareVertex_cutGraph_adj R n
    hwidth hheight hz hw hzw
  have htorus : (fkRectTorusGraph R).Adj
      (fkRectDevelopedSquareVertex R n z)
      (fkRectDevelopedSquareVertex R n w) :=
    ((fkRectCutGraph_adj_iff R _ _).mp hcut).1
  rw [← fkOpenSub_fullGraphConfiguration]
  rw [StatMech.FK.openSub_adj]
  constructor
  · intro hopen
    refine ⟨htorus, ?_⟩
    simpa [fkRectDevelopedSquarePullback] using hopen
  · rintro ⟨_, hopen⟩
    simpa [fkRectDevelopedSquarePullback] using hopen


end
end StatMech.FrontierD
