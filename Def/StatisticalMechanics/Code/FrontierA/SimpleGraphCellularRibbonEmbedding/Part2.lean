module
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
public import Theorem.StatisticalMechanics.Code.FrontierA.SimpleGraphCellularRibbonEmbedding


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SimpleGraphCellularRibbonEmbedding.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def finiteGraphEdge.edgeFlip
    (edge : finiteGraphEdge G) : Equiv.Perm G.Dart :=
  Equiv.swap (edge.dart G) (edge.dart G).symm

end StatMech.FrontierA
