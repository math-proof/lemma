module
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderAdaptiveProjection
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderPlanarization.Part8
public import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderTailPower
public import Theorem.StatisticalMechanics.Code.Probability.AdaptiveFibreStep
public import Theorem.StatisticalMechanics.Code.Probability.FiniteWitnessInsertionIteration
public import Theorem.StatisticalMechanics.Code.FK.ConditionalFibreMass
public import Theorem.StatisticalMechanics.Code.FK.BoxConnectionFullConnection
open MeasureTheory SimpleGraph StatMech.Lattice


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderAdaptiveStep.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def FKRectHorizontalCylinderAdaptivePairedConnectionEvent
    (R : FKRectTorus) (S : Finset (Fin R.width))
    (x targetX : Fin R.width) (psi : ConfigSpace (Sym2 R.Vertex)) :
    Set (ConfigSpace (Sym2 R.Vertex)) :=
  {rho | ∃ source target :
      FKRectHorizontalCylinderUnexploredVertex R psi S,
    source.1 = (x, fkRectBottomRow R) ∧
    target.1 = (targetX, fkRectTopRow R) ∧
    (FK.openSub
      (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) psi
        (fkRectHorizontalCylinderBottomRoots R S))
      (FK.ocd_innerRestrict
        (Subtype.val :
          FKRectHorizontalCylinderUnexploredVertex R psi S → R.Vertex)
        rho)).Reachable source target}


end
end StatMech.FrontierD
