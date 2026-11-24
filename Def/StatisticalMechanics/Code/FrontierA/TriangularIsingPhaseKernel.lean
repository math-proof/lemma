module
public import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalMomentum
public import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingSymbolBounds
public import Theorem.StatisticalMechanics.Code.Onsager.PhaseRegularity.Part12
public import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingPhaseKernel
open Filter MeasureTheory Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingPhaseKernel.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

noncomputable section

def triangularIsingCriticalInverseSymbol
    (beta J p q : Real) : Real :=
  1 / triangularIsingSymbol beta beta (beta * J) p q


end
end StatMech.FrontierA
