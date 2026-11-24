module
public import Theorem.StatisticalMechanics.Code.FK.TriangularSharpness.Part5
public import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
public import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedDomainActive
public import Theorem.StatisticalMechanics.Code.FK.TriangularOffCentre
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

abbrev triangularTransBox (R : Nat) (x : Site 2) : Set (Site 2) :=
  StatMech.FK.fvs_transBox 2 R x

abbrev TriangularTransBoxVertex (R : Nat) (x : Site 2) :=
  {y : Site 2 // y ∈ triangularTransBox R x}

end
end StatMech.FK.PeriodicPlanar
