/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderPlanarization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderExploration
import Theorem.StatisticalMechanics.Code.FrontierD.FKFreeConnectionBoxEmbedding
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingEvent.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulHorizontalExtension
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulCarrierDisjoint
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulShearCoordinates
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulWalkVerticalBound
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusDisjointWinding.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderPlanarization.Part7
open Finset SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem fkRectHorizontalCylinderUnexploredConnection_freeMass_le_boxConn
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    (P : FKRectHorizontalCylinderUnexploredPlanarization R rho S)
    (source target : FKRectHorizontalCylinderUnexploredVertex R rho S)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    (∑ omega,
        (FKFiniteConnectionEvent
          (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
            (fkRectHorizontalCylinderBottomRoots R S)) source target).indicator
          (fun _ => (1 : Real)) omega *
        FK.fkProb
          (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho
            (fkRectHorizontalCylinderBottomRoots R S)) p q omega) ≤
      (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        MeasureTheory.Measure
          (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))).real
        (FK.boxConnEvent 2 P.radius
          (P.embedding source) (P.embedding target)) := by
  exact fkFiniteConnection_freeMass_le_boxConn _ P.radius P.embedding
    P.injective P.adjMatch source target hp hp1 hq


theorem fkRectHorizontalCylinder_conditionalConnection_le_boxConn
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (S : Finset (Fin R.width))
    (P : FKRectHorizontalCylinderUnexploredPlanarization R rho S)
    (source target : FKRectHorizontalCylinderUnexploredVertex R rho S)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    (∑ sigma : ConfigSpace (Sym2 R.Vertex),
        (FK.ocd_innerRestrict
          (Subtype.val :
            FKRectHorizontalCylinderUnexploredVertex R rho S → R.Vertex) ⁻¹'
          FKFiniteConnectionEvent
            (FK.clusterUnexploredGraph
              (fkRectHorizontalCylinderGraph R) rho
              (fkRectHorizontalCylinderBottomRoots R S))
            source target).indicator (fun _ => (1 : Real)) sigma *
        FK.condBcProb (fkRectHorizontalCylinderGraph R)
          (StatMech.Lattice.boundaryCliqueGraph
            (fun _ : R.Vertex => False)) p q
          (FK.clusterUnexploredPairEdges
            (fkRectHorizontalCylinderGraph R) rho
            (fkRectHorizontalCylinderBottomRoots R S)) rho sigma) ≤
      (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        MeasureTheory.Measure
          (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))).real
        (FK.boxConnEvent 2 P.radius
          (P.embedding source) (P.embedding target)) := by
  rw [fkRectHorizontalCylinder_condBcProb_innerEvent_eq_freeUnexplored
    R rho S hp hp1 (zero_lt_one.trans_le hq)]
  exact fkRectHorizontalCylinderUnexploredConnection_freeMass_le_boxConn
    R rho S P source target hp hp1 hq


theorem fkRectHorizontalCylinder_bottom_top_verticalDisplacement
    (R : FKRectTorus) (x y : Fin R.width) :
    ((y, fkRectTopRow R).2.val : Int) -
        ((x, fkRectBottomRow R).2.val : Int) = R.height - 1 := by
  have hh := R.height_pos
  simp [fkRectTopRow, fkRectBottomRow]
  omega

end
end StatMech.FrontierD
