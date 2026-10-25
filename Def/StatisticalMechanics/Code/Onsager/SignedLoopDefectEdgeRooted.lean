/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopDefectEdgeRooted.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopSourceRootedDerivative.Part2
open scoped BigOperators
open Finset SimpleGraph Filter


namespace StatMech.Onsager

open StatMech.FrontierA StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def onsDefectEdgeDart {u v : V} (huv : u ≠ v) :
    (onsDefectEdgeGraph G u v).Dart := by
  refine ⟨(u, v), ?_⟩
  rw [onsDefectEdgeGraph, SimpleGraph.sup_adj, SimpleGraph.edge_adj]
  exact Or.inr ⟨Or.inl ⟨rfl, rfl⟩, huv⟩


def onsDefectEdgeAddedWeight (u v : V) (x : Real)
    (edge : Sym2 V) : Complex :=
  if edge = s(u, v) then 1 else (x : Complex)


end
end StatMech.Onsager
