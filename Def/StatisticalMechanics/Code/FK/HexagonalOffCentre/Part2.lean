/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriangularOffCentre.Part5
import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpness.Part5
import Instance.StatisticalMechanics.Code.FK.HexagonalOffCentre
open scoped BigOperators Classical
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.FiniteGraphBoundaryDifferential

noncomputable section

def hexagonalTransBoxEmbedding (R : Nat) (x : Site 2) :
    HexagonalTransBoxVertex R x → HexVertex :=
  Subtype.val

def hexagonalTransBoxGraph (R : Nat) (x : Site 2) :
    SimpleGraph (HexagonalTransBoxVertex R x) :=
  SimpleGraph.comap (hexagonalTransBoxEmbedding R x) hexagonalGraph

end
end StatMech.FK.PeriodicPlanar
