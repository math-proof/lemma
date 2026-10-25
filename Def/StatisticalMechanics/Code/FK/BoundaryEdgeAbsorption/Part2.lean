/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryEdgeAbsorption.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredWeights.Part4
import Abbrev.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.FK

open StatMech.Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
  (boundary : V -> Prop) [DecidablePred boundary]

def activeGraphInnerEdgeEquiv (hGH : G <= H) :
    G.edgeSet ≃ {e : H.edgeSet // e.1 ∈ G.edgeSet} where
  toFun e := ⟨activeGraphEdgeIncl G H hGH e, e.2⟩
  invFun e := ⟨e.1.1, e.2⟩
  left_inv _ := rfl
  right_inv _ := rfl


def activeGraphEdgeSplitEquiv (hGH : G <= H) :
    H.edgeSet ≃ G.edgeSet ⊕ AddedEdge G H :=
  (((activeGraphInnerEdgeEquiv G H hGH).sumCongr
      (Equiv.refl (AddedEdge G H))).trans
    (Equiv.sumCompl (fun e : H.edgeSet => e.1 ∈ G.edgeSet))).symm


def activeGraphConfigSplitEquiv (hGH : G <= H) :
    ConfigSpace H.edgeSet ≃
      ConfigSpace G.edgeSet × ConfigSpace (AddedEdge G H) where
  toFun eta :=
    (fun e => eta ((activeGraphEdgeSplitEquiv G H hGH).symm (Sum.inl e)),
      fun e => eta ((activeGraphEdgeSplitEquiv G H hGH).symm (Sum.inr e)))
  invFun pair e :=
    match activeGraphEdgeSplitEquiv G H hGH e with
    | Sum.inl a => pair.1 a
    | Sum.inr a => pair.2 a
  left_inv eta := by
    funext e
    rcases h : activeGraphEdgeSplitEquiv G H hGH e with a | a
    · simp only [h]
      rw [show (activeGraphEdgeSplitEquiv G H hGH).symm (Sum.inl a) = e by
        rw [← h]; exact (activeGraphEdgeSplitEquiv G H hGH).symm_apply_apply e]
    · simp only [h]
      rw [show (activeGraphEdgeSplitEquiv G H hGH).symm (Sum.inr a) = e by
        rw [← h]; exact (activeGraphEdgeSplitEquiv G H hGH).symm_apply_apply e]
  right_inv pair := by
    apply Prod.ext <;> funext e
    · simp [activeGraphEdgeSplitEquiv, activeGraphInnerEdgeEquiv,
        activeGraphEdgeIncl]
    · simp [activeGraphEdgeSplitEquiv, activeGraphInnerEdgeEquiv,
        activeGraphEdgeIncl]

end
end StatMech.FK
