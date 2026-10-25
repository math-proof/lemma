/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SimpleGraphCellularRibbonEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.SimpleGraphCellularRibbonEmbedding.Part2


namespace StatMech.FrontierA

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


structure FiniteCellularGraphEmbedding where
  rotation : Equiv.Perm G.Dart
  rotation_fst : forall dart, (rotation dart).fst = dart.fst
  rotationCycles_eq_vertices :
    permCycleCount rotation = Fintype.card V
  faceCount : Nat
  genus : Nat
  cellularEuler :
    Fintype.card V + faceCount + 2 * genus = G.edgeFinset.card + 2

end StatMech.FrontierA
