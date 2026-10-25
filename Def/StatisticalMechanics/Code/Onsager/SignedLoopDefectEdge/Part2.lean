/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopDefectEdge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopTwoPointAudit
import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSwitching.Part4
import Instance.StatisticalMechanics.Code.Onsager.SignedLoopDefectEdge
open scoped BigOperators symmDiff
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def ons_defectEdgeX (u v : V) (x z : Real) : Real :=
  let e := s(u, v)
  ∑ F ∈ (insert e G.edgeFinset).powerset.filter IsEvenSubgraph,
    (if e ∈ F then z else 1) * x ^ (F.erase e).card

end StatMech.Onsager
