/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriangularOffCentre.Part5
import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpness.Part5
import Theorem.StatisticalMechanics.Code.FK.HexagonalOffCentre
open scoped BigOperators Classical
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.FiniteGraphBoundaryDifferential

noncomputable section

def hexagonalTransBoxBoundary (R : Nat) (x : Site 2)
    (y : HexagonalTransBoxVertex R x) : Prop :=
  y.1.1 - x ∈ vertexBoundary 2 R

noncomputable def hexagonalTransBoxShell (R k : Nat) (x : Site 2) :
    Finset (HexagonalTransBoxVertex R x) :=
  Finset.univ.filter fun y => y.1.1 - x ∈ vertexBoundary 2 k

def hexagonalTransBoxCenter (R : Nat) (x : HexVertex) :
    HexagonalTransBoxVertex R x.1 :=
  ⟨x, by simp [StatMech.FK.fvs_transBox]⟩

def hexagonalReflect (y : HexVertex) : HexVertex := (-y.1, !y.2)

end
end StatMech.FK.PeriodicPlanar
