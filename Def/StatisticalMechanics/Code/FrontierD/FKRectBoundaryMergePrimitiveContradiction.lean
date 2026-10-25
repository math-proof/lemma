/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryMergePrimitiveContradiction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryToggleMergeWinding
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonPrimitive
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedAnchor.Part11
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def fkRectBoundaryMergeOldWinding0
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex) :
    Int × Int :=
  fkRectBlackBoundaryCycleClassWinding R
    (fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R F))
    (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e))

def fkRectBoundaryMergeOldWinding1
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex) :
    Int × Int :=
  fkRectBlackBoundaryCycleClassWinding R
    (fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R F))
    (fkMedialBlackDart1 (fkRectMedialVertexOfEdge R e))

def fkRectBoundaryMergeNewWinding
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex) :
    Int × Int :=
  fkRectBlackBoundaryCycleClassWinding R
    (fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R (insert e F)))
    (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e))

def fkRectBoundarySplitNewWinding1
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex) :
    Int × Int :=
  fkRectBlackBoundaryCycleClassWinding R
    (fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R (insert e F)))
    (fkMedialBlackDart1 (fkRectMedialVertexOfEdge R e))


end
end StatMech.FrontierD
