/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamAgreementVBG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part11
import Theorem.StatisticalMechanics.Code.Walls.vbgtriangle.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamImprovementBridge
open Finset SimpleGraph
open scoped BigOperators
open Classical


namespace StatMech.FrontierA

open StatMech.ConfigSpace StatMech.Ising StatMech.Walls

open StatMech.Walls.VBG

open StatMech.Walls.GhcEqGap StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def grahamReplicaAgree (a b : ConfigSpace V) (k : V) : Real :=
  if a k = b k then 1 else 0

end StatMech.FrontierA
