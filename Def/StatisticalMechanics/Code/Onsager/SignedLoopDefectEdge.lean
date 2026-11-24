module
public import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopTwoPointAudit
public import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSwitching.Part4
open scoped BigOperators symmDiff
open Finset SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopDefectEdge.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Onsager

open StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def onsDefectEdgeGraph (u v : V) : SimpleGraph V := G ⊔ SimpleGraph.edge u v

end StatMech.Onsager
