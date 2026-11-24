module
public import Theorem.StatisticalMechanics.Code.FK.ActiveBoundaryEdges
public import Theorem.StatisticalMechanics.Code.FK.EdgeConfigZ.Part15
public import Theorem.StatisticalMechanics.Code.FK.IvProperties
open scoped BigOperators Classical
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ActiveBoundaryEquiv.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable (C : SimpleGraph V) [DecidableRel C.Adj]


def restrictActive (omega : ConfigSpace (Sym2 V)) : ConfigSpace G.edgeSet :=
  fun e => omega e.1

end FK
end StatMech
