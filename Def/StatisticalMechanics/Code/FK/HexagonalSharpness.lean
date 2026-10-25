/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FiniteGraphBoundaryDifferential
import Theorem.StatisticalMechanics.Code.OSSS.DecisionTreeReindex
import Theorem.StatisticalMechanics.Code.FK.TriHexCoarseGeometry.Part3
import Instance.StatisticalMechanics.Code.FK.HexagonalSharpness
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS RevealmentConstruction LindebergTree DecisionTree

open StatMech.OSSS.FiniteGraphBoundaryDifferential

def hexagonalBoxEmbedding (n : Nat) : HexagonalBoxVertex n → HexVertex :=
  Subtype.val

def hexagonalBoxGraph (n : Nat) : SimpleGraph (HexagonalBoxVertex n) :=
  SimpleGraph.comap (hexagonalBoxEmbedding n) hexagonalGraph

end StatMech.FK.PeriodicPlanar
