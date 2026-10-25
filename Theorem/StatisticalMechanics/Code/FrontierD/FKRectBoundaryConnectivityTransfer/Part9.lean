/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Theorem.StatisticalMechanics.Code.Foundations.FiniteNonnegativeMatrixRate.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part10
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


@[simp] theorem fkRectLayerCollapse_inputEmbed {W : Nat}
    (u : Bool × Fin W) :
    fkRectLayerCollapse (fkRectLayerInputEmbed u) = u := by
  rcases u with ⟨b, x⟩
  cases b <;> simp [fkRectLayerCollapse, fkRectLayerInputEmbed,
    fkRectLayerInitialRole, fkRectLayerOldRole]

@[simp] theorem fkRectLayerCollapse_outputEmbed {W : Nat}
    (u : Bool × Fin W) :
    fkRectLayerCollapse (fkRectLayerOutputEmbed u) = u := by
  rcases u with ⟨b, x⟩
  cases b <;> simp [fkRectLayerCollapse, fkRectLayerOutputEmbed,
    fkRectLayerInitialRole, fkRectLayerNewRole]

theorem fkRectBoundaryVerticalLayer_adj_collapse_reachable
    {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (state : FKRectBoundaryState W) {u v : FKRectLayerVertex W}
    (huv : (fkRectBoundaryLayerGraph hW evenRow state
      fkRectBoundaryVerticalLayer).Adj u v) :
    state.Reachable (fkRectLayerCollapse u) (fkRectLayerCollapse v) := by
  rcases huv with hstate | hedge
  · obtain ⟨x, y, hxy, rfl, rfl⟩ := hstate
    simpa using hxy.reachable
  · obtain ⟨a, ha, huv | huv⟩ := hedge
    all_goals
      rcases a with ⟨dir, x⟩
      cases dir
      · simp [fkRectBoundaryVerticalLayer] at ha
      · rcases huv with ⟨rfl, rfl⟩
        simp [fkRectLayerEdgeEndpoints, fkRectLayerCollapse,
          fkRectLayerOldRole, fkRectLayerNewRole,
          fkRectLayerInitialRole]

theorem fkRectBoundaryVerticalLayer_reachable_collapse
    {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (state : FKRectBoundaryState W) {u v : FKRectLayerVertex W}
    (huv : (fkRectBoundaryLayerGraph hW evenRow state
      fkRectBoundaryVerticalLayer).Reachable u v) :
    state.Reachable (fkRectLayerCollapse u) (fkRectLayerCollapse v) := by
  rcases huv with ⟨p⟩
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj p ih =>
      exact (fkRectBoundaryVerticalLayer_adj_collapse_reachable
        hW evenRow state hadj).trans ih

theorem fkRectBoundaryVerticalLayer_input_reachable
    {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (state : FKRectBoundaryState W) {u v : Bool × Fin W}
    (huv : state.Reachable u v) :
    (fkRectBoundaryLayerGraph hW evenRow state
      fkRectBoundaryVerticalLayer).Reachable
        (fkRectLayerInputEmbed u) (fkRectLayerInputEmbed v) := by
  rcases huv with ⟨p⟩
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj p ih =>
      exact (show (fkRectBoundaryLayerGraph hW evenRow state
        fkRectBoundaryVerticalLayer).Adj
          (fkRectLayerInputEmbed _) (fkRectLayerInputEmbed _) from
            Or.inl ⟨_, _, hadj, rfl, rfl⟩).reachable.trans ih

theorem fkRectBoundaryVerticalLayer_input_output_reachable
    {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (state : FKRectBoundaryState W) (u : Bool × Fin W) :
    (fkRectBoundaryLayerGraph hW evenRow state
      fkRectBoundaryVerticalLayer).Reachable
        (fkRectLayerInputEmbed u) (fkRectLayerOutputEmbed u) := by
  rcases u with ⟨b, x⟩
  cases b
  · exact SimpleGraph.Reachable.refl _
  · apply SimpleGraph.Adj.reachable
    exact Or.inr ⟨(true, x), rfl, Or.inl ⟨by
      simp [fkRectLayerEdgeEndpoints, fkRectLayerInputEmbed,
        fkRectLayerOldRole], by
      simp [fkRectLayerEdgeEndpoints, fkRectLayerOutputEmbed,
        fkRectLayerNewRole]⟩⟩

theorem fkRectBoundaryVerticalLayer_output_reachable_iff
    {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (state : FKRectBoundaryState W) (u v : Bool × Fin W) :
    (fkRectBoundaryLayerGraph hW evenRow state
      fkRectBoundaryVerticalLayer).Reachable
        (fkRectLayerOutputEmbed u) (fkRectLayerOutputEmbed v) ↔
      state.Reachable u v := by
  constructor
  · intro h
    simpa using fkRectBoundaryVerticalLayer_reachable_collapse
      hW evenRow state h
  · intro h
    exact (fkRectBoundaryVerticalLayer_input_output_reachable
      hW evenRow state u).symm.trans
        ((fkRectBoundaryVerticalLayer_input_reachable
          hW evenRow state h).trans
          (fkRectBoundaryVerticalLayer_input_output_reachable
            hW evenRow state v))


theorem fkRectBoundaryLayerOutput_vertical
    {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (state : FKRectBoundaryState W) (hstate : state.IsConnectivity) :
    fkRectBoundaryLayerOutput hW evenRow state
      fkRectBoundaryVerticalLayer = state := by
  ext u v
  rw [hstate]
  exact and_congr_right fun _ =>
    fkRectBoundaryVerticalLayer_output_reachable_iff
      hW evenRow state u v


end
end StatMech.FrontierD
