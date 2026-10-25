/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularOffCentre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriangularSharpness.Part5
import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedDomainActive
import Theorem.StatisticalMechanics.Code.FK.TriangularOffCentre.Part2
open scoped BigOperators Classical
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.FiniteGraphBoundaryDifferential

noncomputable section

def triangularTransBoxBoundary (R : Nat) (x : Site 2)
    (y : TriangularTransBoxVertex R x) : Prop :=
  y.1 - x ∈ vertexBoundary 2 R

noncomputable def triangularTransBoxShell (R k : Nat) (x : Site 2) :
    Finset (TriangularTransBoxVertex R x) :=
  Finset.univ.filter fun y => y.1 - x ∈ vertexBoundary 2 k

def triangularTransBoxCenter (R : Nat) (x : Site 2) :
    TriangularTransBoxVertex R x :=
  ⟨x, by simp [StatMech.FK.fvs_transBox]⟩


end
end StatMech.FK.PeriodicPlanar
