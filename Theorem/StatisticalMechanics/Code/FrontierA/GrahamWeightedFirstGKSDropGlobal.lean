/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamWeightedFirstGKSDropGlobal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedFirstGKSDrop
open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000


namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem grahamCurrentConnected_add_right
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p q : G.edgeFinset -> Nat) {u v : V}
    (h : CurrentConnected G (ofEdgeFun G p) u v) :
    CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) u v := by
  exact SimpleGraph.Reachable.mono (fun a b hab => by
    refine ⟨hab.1, ?_⟩
    have hedge : s(a, b) ∈ G.edgeFinset := by
      simpa [SimpleGraph.mem_edgeFinset] using hab.1
    calc
      1 ≤ ofEdgeFun G p s(a, b) := hab.2
      _ = p ⟨s(a, b), hedge⟩ := by simp [ofEdgeFun, hedge]
      _ ≤ p ⟨s(a, b), hedge⟩ + q ⟨s(a, b), hedge⟩ :=
        Nat.le_add_right _ _
      _ = ofEdgeFun G (fun e => p e + q e) s(a, b) := by
        simp [ofEdgeFun, hedge]) h


end StatMech.FrontierA
