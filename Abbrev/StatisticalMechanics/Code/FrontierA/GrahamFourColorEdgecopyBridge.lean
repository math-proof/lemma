/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorEdgecopyBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorProfileCount.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedFourReplicaCore
open Finset SimpleGraph
open scoped BigOperators
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness.FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

abbrev GrahamFourSplit (total : G.edgeFinset -> Nat) :=
  {pqr : (G.edgeFinset -> Nat) × (G.edgeFinset -> Nat) ×
      (G.edgeFinset -> Nat) //
    forall e, pqr.1 e + pqr.2.1 e + pqr.2.2 e <= total e}


end StatMech.FrontierA
