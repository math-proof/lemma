/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopTwoPointAudit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.HighTemp
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCriticalWeight
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSources.Part3
open scoped BigOperators
open Finset


namespace StatMech.Onsager

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def ons_sourceX (A : Finset V) (x : Real) : Real :=
  ∑ F ∈ G.edgeFinset.powerset.filter
      (fun F => StatMech.Sharpness.HasOddBoundary F A),
    x ^ F.card


end StatMech.Onsager
