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
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part24
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


theorem fkRectBoundaryInitialState_component_count (W : Nat) :
    Nat.card (fkRectBoundaryInitialState W).ConnectedComponent = W := by
  rw [Nat.card_congr (fkRectBoundaryInitialComponentEquiv W), Nat.card_fin]

theorem fkRectStripState_isConnectivity
    {W : Nat} (hW : 0 < W) (n : Nat)
    (layers : Fin n -> Bool × (Bool × Fin W -> Bool)) :
    (fkRectStripState hW n layers).IsConnectivity := by
  cases n with
  | zero =>
      simpa [fkRectStripState] using fkRectBoundaryInitialState_isConnectivity W
  | succ n =>
      simp only [fkRectStripState]
      exact fkRectBoundaryLayerOutput_isConnectivity _ _ _ _

theorem fkRectBoundaryEmptyLayer_reachable_new_iff
    {W : Nat} (hW : 0 < W) (evenRow : Bool)
    (state : FKRectBoundaryState W) (v : FKRectLayerVertex W) (x : Fin W) :
    (fkRectBoundaryLayerGraph hW evenRow state
      fkRectBoundaryEmptyLayer).Reachable v (fkRectLayerNewRole, x) ↔
      v = (fkRectLayerNewRole, x) := by
  rw [SimpleGraph.reachable_comm,
    fkRectBoundaryEmptyLayer_new_reachable_iff]


theorem fkRectStripExpanded_reachable_iff
    {W : Nat} (hW : 0 < W) (n : Nat)
    (layers : Fin n -> Bool × (Bool × Fin W -> Bool))
    (evenRow : Bool)
    (hprev : ∀ u v : Bool × Fin W,
      ((fkRectStripGraph hW n layers).Reachable
        (fkRectStripBoundary n u) (fkRectStripBoundary n v) ↔
          (fkRectStripState hW n layers).Reachable u v))
    (u v : FKRectLayerVertex W) :
    ((fkRectStripGraph hW n layers).sum (⊥ : SimpleGraph (Fin W))).Reachable
        (fkRectStripLayerEmbed n u) (fkRectStripLayerEmbed n v) ↔
      (fkRectBoundaryLayerGraph hW evenRow
        (fkRectStripState hW n layers) fkRectBoundaryEmptyLayer).Reachable
          u v := by
  rcases u with ⟨i, x⟩
  rcases v with ⟨j, y⟩
  fin_cases i <;> fin_cases j
  · simpa [fkRectStripLayerEmbed, fkRectLayerInputEmbed,
      fkRectLayerInitialRole, fkRectLayerOldRole, fkRectStripBoundary,
      simpleGraph_sum_reachable_inl_iff] using
        (hprev (false, x) (false, y)).trans
          (fkRectBoundaryEmptyLayer_input_reachable_iff hW evenRow
            (fkRectStripState hW n layers) (false, x) (false, y)).symm
  · simpa [fkRectStripLayerEmbed, fkRectLayerInputEmbed,
      fkRectLayerInitialRole, fkRectLayerOldRole, fkRectStripBoundary,
      simpleGraph_sum_reachable_inl_iff] using
        (hprev (false, x) (true, y)).trans
          (fkRectBoundaryEmptyLayer_input_reachable_iff hW evenRow
            (fkRectStripState hW n layers) (false, x) (true, y)).symm
  · simp [fkRectStripLayerEmbed, fkRectLayerInitialRole,
      fkRectLayerOldRole, fkRectLayerNewRole,
      simpleGraph_sum_not_reachable_inl_inr]
    simpa [fkRectLayerInitialRole, fkRectLayerNewRole] using
      (fkRectBoundaryEmptyLayer_reachable_new_iff hW evenRow
        (fkRectStripState hW n layers)
        (fkRectLayerInitialRole, x) y).not
  · simpa [fkRectStripLayerEmbed, fkRectLayerInputEmbed,
      fkRectLayerInitialRole, fkRectLayerOldRole, fkRectStripBoundary,
      simpleGraph_sum_reachable_inl_iff] using
        (hprev (true, x) (false, y)).trans
          (fkRectBoundaryEmptyLayer_input_reachable_iff hW evenRow
            (fkRectStripState hW n layers) (true, x) (false, y)).symm
  · simpa [fkRectStripLayerEmbed, fkRectLayerInputEmbed,
      fkRectLayerInitialRole, fkRectLayerOldRole, fkRectStripBoundary,
      simpleGraph_sum_reachable_inl_iff] using
        (hprev (true, x) (true, y)).trans
          (fkRectBoundaryEmptyLayer_input_reachable_iff hW evenRow
            (fkRectStripState hW n layers) (true, x) (true, y)).symm
  · simp [fkRectStripLayerEmbed, fkRectLayerInitialRole,
      fkRectLayerOldRole, fkRectLayerNewRole,
      simpleGraph_sum_not_reachable_inl_inr]
    simpa [fkRectLayerOldRole, fkRectLayerNewRole] using
      (fkRectBoundaryEmptyLayer_reachable_new_iff hW evenRow
        (fkRectStripState hW n layers)
        (fkRectLayerOldRole, x) y).not
  · simp [fkRectStripLayerEmbed, fkRectLayerInitialRole,
      fkRectLayerOldRole, fkRectLayerNewRole,
      simpleGraph_sum_not_reachable_inr_inl]
    simpa [fkRectLayerInitialRole, fkRectLayerNewRole] using
      (fkRectBoundaryEmptyLayer_new_reachable_iff hW evenRow
        (fkRectStripState hW n layers) x
        (fkRectLayerInitialRole, y)).not
  · simp [fkRectStripLayerEmbed, fkRectLayerInitialRole,
      fkRectLayerOldRole, fkRectLayerNewRole,
      simpleGraph_sum_not_reachable_inr_inl]
    simpa [fkRectLayerOldRole, fkRectLayerNewRole] using
      (fkRectBoundaryEmptyLayer_new_reachable_iff hW evenRow
        (fkRectStripState hW n layers) x
        (fkRectLayerOldRole, y)).not
  · change (((fkRectStripGraph hW n layers).sum
        (⊥ : SimpleGraph (Fin W))).Reachable (Sum.inr x) (Sum.inr y) ↔
      (fkRectBoundaryLayerGraph hW evenRow
        (fkRectStripState hW n layers) fkRectBoundaryEmptyLayer).Reachable
          (fkRectLayerNewRole, x) (fkRectLayerNewRole, y))
    rw [simpleGraph_sum_reachable_inr_iff, SimpleGraph.reachable_bot]
    simpa [fkRectLayerNewRole, eq_comm] using
      (fkRectBoundaryEmptyLayer_new_reachable_iff hW evenRow
        (fkRectStripState hW n layers) x
        (fkRectLayerNewRole, y)).symm


theorem fkRectStrip_boundary_reachable_iff
    {W : Nat} (hW : 0 < W) (n : Nat)
    (layers : Fin n -> Bool × (Bool × Fin W -> Bool))
    (u v : Bool × Fin W) :
    (fkRectStripGraph hW n layers).Reachable
        (fkRectStripBoundary n u) (fkRectStripBoundary n v) ↔
      (fkRectStripState hW n layers).Reachable u v := by
  induction n generalizing u v with
  | zero =>
      simpa [fkRectStripGraph, fkRectStripBoundary, fkRectStripInitial,
        fkRectStripCurrent, fkRectStripState, SimpleGraph.reachable_bot]
        using (fkRectBoundaryInitialState_reachable_iff W u v).symm
  | succ n ih =>
      let priorLayers : Fin n -> Bool × (Bool × Fin W -> Bool) :=
        fun i => layers i.castSucc
      let layer := layers (Fin.last n)
      have hbase : ∀ x y : FKRectLayerVertex W,
          ((fkRectStripGraph hW n priorLayers).sum
            (⊥ : SimpleGraph (Fin W))).Reachable
              (fkRectStripLayerEmbed n x) (fkRectStripLayerEmbed n y) ↔
            (fkRectBoundaryLayerGraph hW layer.1
              (fkRectStripState hW n priorLayers)
              fkRectBoundaryEmptyLayer).Reachable x y :=
        fkRectStripExpanded_reachable_iff hW n priorLayers layer.1
          (fun x y => ih priorLayers x y)
      change (finiteBoundaryEdgeRun (fkRectStripLayerEmbed n)
          ((fkRectStripGraph hW n priorLayers).sum (⊥ : SimpleGraph (Fin W)))
          (fkRectBoundaryOpenLayerEdges hW layer.1 layer.2)).Reachable
            (fkRectStripBoundary (n + 1) u)
            (fkRectStripBoundary (n + 1) v) ↔
        (fkRectBoundaryLayerOutput hW layer.1
          (fkRectStripState hW n priorLayers) layer.2).Reachable u v
      rw [← fkRectStripLayerEmbed_output n u,
        ← fkRectStripLayerEmbed_output n v]
      rw [finiteBoundaryEdgeRun_reachable_iff
        (fkRectStripLayerEmbed n)
        ((fkRectStripGraph hW n priorLayers).sum (⊥ : SimpleGraph (Fin W)))
        (fkRectBoundaryLayerGraph hW layer.1
          (fkRectStripState hW n priorLayers) fkRectBoundaryEmptyLayer)
        hbase]
      change (finiteBoundaryEdgeRun id
          (fkRectBoundaryLayerGraph hW layer.1
            (fkRectStripState hW n priorLayers) (fun _ => false))
          (fkRectBoundaryOpenLayerEdges hW layer.1 layer.2)).Reachable
            (fkRectLayerOutputEmbed u) (fkRectLayerOutputEmbed v) ↔
        (fkRectBoundaryLayerOutput hW layer.1
          (fkRectStripState hW n priorLayers) layer.2).Reachable u v
      rw [← fkRectBoundaryLayerGraph_eq_edgeRun hW layer.1
        (fkRectStripState hW n priorLayers) layer.2]
      rw [fkRectBoundaryLayerOutput_eq_finiteBoundaryConnectivityGraph,
        finiteBoundaryConnectivityGraph_reachable_iff]


theorem fkRectStrip_component_count
    {W : Nat} (hW : 0 < W) (n : Nat)
    (layers : Fin n -> Bool × (Bool × Fin W -> Bool)) :
    Nat.card (fkRectStripGraph hW n layers).ConnectedComponent =
      fkRectStripClosedCount hW n layers +
        Nat.card (fkRectStripState hW n layers).ConnectedComponent := by
  induction n with
  | zero =>
      rw [fkRectStripGraph, StatMech.Lattice.card_components_bot]
      have hvertices : Nat.card (FKRectStripVertex W 0) = W := by
        change Nat.card (Fin W) = W
        exact Nat.card_fin W
      rw [hvertices, fkRectStripClosedCount, fkRectStripState,
        fkRectBoundaryInitialState_component_count]
      simp
  | succ n ih =>
      let priorLayers : Fin n -> Bool × (Bool × Fin W -> Bool) :=
        fun i => layers i.castSucc
      let layer := layers (Fin.last n)
      let priorGraph := fkRectStripGraph hW n priorLayers
      let priorState := fkRectStripState hW n priorLayers
      let expandedGraph := priorGraph.sum (⊥ : SimpleGraph (Fin W))
      let emptyLayer := fkRectBoundaryLayerGraph hW layer.1 priorState
        fkRectBoundaryEmptyLayer
      have hbase : ∀ x y : FKRectLayerVertex W,
          expandedGraph.Reachable (fkRectStripLayerEmbed n x)
              (fkRectStripLayerEmbed n y) ↔
            emptyLayer.Reachable x y := by
        exact fkRectStripExpanded_reachable_iff hW n priorLayers layer.1
          (fun x y => fkRectStrip_boundary_reachable_iff
            hW n priorLayers x y)
      have hcross := finiteBoundaryEdgeRun_component_cross_sum
        (fkRectStripLayerEmbed n) expandedGraph emptyLayer hbase
        (fkRectBoundaryOpenLayerEdges hW layer.1 layer.2)
      have hExpanded :
          Nat.card expandedGraph.ConnectedComponent =
            fkRectStripClosedCount hW n priorLayers +
              Nat.card priorState.ConnectedComponent + W := by
        rw [simpleGraph_card_components_sum]
        change Nat.card priorGraph.ConnectedComponent +
            Nat.card (⊥ : SimpleGraph (Fin W)).ConnectedComponent = _
        rw [ih priorLayers, StatMech.Lattice.card_components_bot, Nat.card_fin]
      have hEmpty :
          Nat.card emptyLayer.ConnectedComponent =
            Nat.card priorState.ConnectedComponent + W := by
        rw [Nat.card_eq_fintype_card,
          fkRectBoundaryEmptyLayer_component_count hW layer.1 priorState
            (fkRectStripState_isConnectivity hW n priorLayers),
          ← Nat.card_eq_fintype_card]
      have hFull :
          Nat.card (fkRectBoundaryLayerGraph hW layer.1 priorState
            layer.2).ConnectedComponent =
            fkRectBoundaryLayerClosedCount hW layer.1 priorState layer.2 +
              Nat.card (fkRectBoundaryLayerOutput hW layer.1 priorState
                layer.2).ConnectedComponent := by
        rw [Nat.card_eq_fintype_card,
          fkRectBoundaryLayer_component_count,
          ← Nat.card_eq_fintype_card]
      have hLayerGraph : finiteBoundaryEdgeRun id emptyLayer
          (fkRectBoundaryOpenLayerEdges hW layer.1 layer.2) =
            fkRectBoundaryLayerGraph hW layer.1 priorState layer.2 := by
        dsimp only [emptyLayer, fkRectBoundaryEmptyLayer]
        exact (fkRectBoundaryLayerGraph_eq_edgeRun hW layer.1 priorState
          layer.2).symm
      have hStripGraph : finiteBoundaryEdgeRun (fkRectStripLayerEmbed n)
          expandedGraph (fkRectBoundaryOpenLayerEdges hW layer.1 layer.2) =
            fkRectStripGraph hW (n + 1) layers := by
        rfl
      rw [hLayerGraph, hStripGraph] at hcross
      have hcross' :
          (fkRectStripClosedCount hW n priorLayers +
              Nat.card priorState.ConnectedComponent + W) +
            (fkRectBoundaryLayerClosedCount hW layer.1 priorState layer.2 +
              Nat.card (fkRectBoundaryLayerOutput hW layer.1 priorState
                layer.2).ConnectedComponent) =
          (Nat.card priorState.ConnectedComponent + W) +
            Nat.card (fkRectStripGraph hW (n + 1) layers).ConnectedComponent := by
        rw [← hExpanded, ← hFull, ← hEmpty]
        exact hcross
      change Nat.card (fkRectStripGraph hW (n + 1) layers).ConnectedComponent =
        (fkRectStripClosedCount hW n priorLayers +
          fkRectBoundaryLayerClosedCount hW layer.1 priorState layer.2) +
        Nat.card (fkRectBoundaryLayerOutput hW layer.1 priorState
          layer.2).ConnectedComponent
      omega

theorem fkRectBoundaryRunState_append
    {W : Nat} (hW : 0 < W) (state : FKRectBoundaryState W)
    (left right : List (Bool × (Bool × Fin W -> Bool))) :
    fkRectBoundaryRunState hW state (left ++ right) =
      fkRectBoundaryRunState hW
        (fkRectBoundaryRunState hW state left) right := by
  induction left generalizing state with
  | nil => rfl
  | cons layer left ih =>
      simp only [List.cons_append, fkRectBoundaryRunState]
      exact ih _

theorem fkRectBoundaryRunClosedCount_append
    {W : Nat} (hW : 0 < W) (state : FKRectBoundaryState W)
    (left right : List (Bool × (Bool × Fin W -> Bool))) :
    fkRectBoundaryRunClosedCount hW state (left ++ right) =
      fkRectBoundaryRunClosedCount hW state left +
        fkRectBoundaryRunClosedCount hW
          (fkRectBoundaryRunState hW state left) right := by
  induction left generalizing state with
  | nil => simp [fkRectBoundaryRunClosedCount, fkRectBoundaryRunState]
  | cons layer left ih =>
      simp only [List.cons_append, fkRectBoundaryRunClosedCount,
        fkRectBoundaryRunState]
      rw [ih]
      omega

theorem fkRectStripState_eq_runState
    {W : Nat} (hW : 0 < W) (n : Nat)
    (layers : Fin n -> Bool × (Bool × Fin W -> Bool)) :
    fkRectStripState hW n layers =
      fkRectBoundaryRunState hW (fkRectBoundaryInitialState W)
        (List.ofFn layers) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.ofFn_succ_last,
        fkRectBoundaryRunState_append, ← ih]
      rfl

theorem fkRectStripClosedCount_eq_runClosedCount
    {W : Nat} (hW : 0 < W) (n : Nat)
    (layers : Fin n -> Bool × (Bool × Fin W -> Bool)) :
    fkRectStripClosedCount hW n layers =
      fkRectBoundaryRunClosedCount hW (fkRectBoundaryInitialState W)
        (List.ofFn layers) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.ofFn_succ_last,
        fkRectBoundaryRunClosedCount_append, ← ih,
        ← fkRectStripState_eq_runState]
      rfl


end
end StatMech.FrontierD
