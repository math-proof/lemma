module
public import Theorem.StatisticalMechanics.Code.FK.TriangularSharpness.Part5
public import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
public import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedDomainActive
public import Abbrev.StatisticalMechanics.Code.FK.TriangularOffCentre
open scoped BigOperators Classical
open Finset Set SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularOffCentre.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.FiniteGraphBoundaryDifferential

noncomputable section

def triangularTransBoxGraph (R : Nat) (x : Site 2) :
    SimpleGraph (TriangularTransBoxVertex R x) :=
  SimpleGraph.comap Subtype.val triangularGraph

end
end StatMech.FK.PeriodicPlanar
