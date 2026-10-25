/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FiniteBipartiteFlowSparse.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
open Finset


namespace StatMech.FrontierD

def bipartiteEdgeIncidenceGraph
    {E P D : Type*} (left : E → P) (right : E → D) : SimpleGraph E where
  Adj e f := e ≠ f ∧ (left e = left f ∨ right e = right f)
  symm := by
    constructor
    rintro e f ⟨hef, hleft | hright⟩
    · exact ⟨hef.symm, Or.inl hleft.symm⟩
    · exact ⟨hef.symm, Or.inr hright.symm⟩
  loopless := ⟨by
    intro e h
    exact h.1 rfl⟩


end StatMech.FrontierD
