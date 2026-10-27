import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part41
open Finset Matrix Filter Topology StatMech StatMech.FrontierD


/--
[finiteBoundaryConnectivityGraph_reachable_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma finiteBoundaryConnectivityGraph_reachable_iff_eq
  {G : SimpleGraph V}
  {u v : B}
-- given
  (embed : B -> V) :
-- imply
  (finiteBoundaryConnectivityGraph G embed).Reachable u v ↔ G.Reachable (embed u) (embed v) := by
-- proof
  apply StatMech.FrontierD.finiteBoundaryConnectivityGraph_reachable_iff G embed u v

/--
[finite_component_count_eq_closed_add_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma finite_component_count_eq_closed_add_boundary_eq
  [Fintype V]
  [Fintype B]
  [DecidableEq V]
  [DecidableEq B]
  {G : SimpleGraph V}
-- given
  (embed : B -> V) :
-- imply
  Fintype.card G.ConnectedComponent = (Finset.univ.filter fun C : G.ConnectedComponent => ∀ u : B, G.connectedComponentMk (embed u) ≠ C).card + Fintype.card (finiteBoundaryConnectivityGraph G embed).ConnectedComponent := by
-- proof
  apply StatMech.FrontierD.finite_component_count_eq_closed_add_boundary G embed

/--
[finiteBoundaryEdgeRun_adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma finiteBoundaryEdgeRun_adj_iff_eq
  {G : SimpleGraph V}
  {edges : List (B × B)}
  {u v : V}
-- given
  (embed : B -> V) :
-- imply
  (finiteBoundaryEdgeRun embed G edges).Adj u v ↔ G.Adj u v ∨ ∃ e ∈ edges, (SimpleGraph.edge (embed e.1) (embed e.2)).Adj u v := by
-- proof
  apply StatMech.FrontierD.finiteBoundaryEdgeRun_adj_iff embed G edges u v

/--
[finiteBoundaryEdgeRun_reachable_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma finiteBoundaryEdgeRun_reachable_iff_eq
  {G : SimpleGraph V}
  {K : SimpleGraph B}
  {edges : List (B × B)}
  {x y : B}
-- given
  (embed : B -> V)
  (hreach : ∀ x y, G.Reachable (embed x) (embed y) ↔ K.Reachable x y) :
-- imply
  (finiteBoundaryEdgeRun embed G edges).Reachable (embed x) (embed y) ↔ (finiteBoundaryEdgeRun id K edges).Reachable x y := by
-- proof
  apply StatMech.FrontierD.finiteBoundaryEdgeRun_reachable_iff embed G K hreach edges x y

/--
[finiteBoundaryEdgeRun_component_cross_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma finiteBoundaryEdgeRun_component_cross_sum_eq
  [Fintype V]
  [Fintype B]
  [DecidableEq V]
  [DecidableEq B]
  {G : SimpleGraph V}
  {K : SimpleGraph B}
  {edges : List (B × B)}
-- given
  (embed : B -> V)
  (hreach : ∀ x y, G.Reachable (embed x) (embed y) ↔ K.Reachable x y) :
-- imply
  Nat.card G.ConnectedComponent + Nat.card (finiteBoundaryEdgeRun id K edges).ConnectedComponent = Nat.card K.ConnectedComponent + Nat.card (finiteBoundaryEdgeRun embed G edges).ConnectedComponent := by
-- proof
  apply StatMech.FrontierD.finiteBoundaryEdgeRun_component_cross_sum embed G K hreach edges

/--
[fkRectConfigurationLayersEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectConfigurationLayersEquiv_apply_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {y : Fin R.height} :
-- imply
  fkRectConfigurationLayersEquiv R omega y = fkRectConfigurationLayer R omega y := by
-- proof
  apply StatMech.FrontierD.fkRectConfigurationLayersEquiv_apply R omega y

/--
[fkRectLayerInputEmbed_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectLayerInputEmbed_injective_eq
  {W : Nat} :
-- imply
  Function.Injective (fkRectLayerInputEmbed : Bool × Fin W -> FKRectLayerVertex W) := by
-- proof
  apply StatMech.FrontierD.fkRectLayerInputEmbed_injective

/--
[fkRectLayerOutputEmbed_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectLayerOutputEmbed_injective_eq
  {W : Nat} :
-- imply
  Function.Injective (fkRectLayerOutputEmbed : Bool × Fin W -> FKRectLayerVertex W) := by
-- proof
  apply StatMech.FrontierD.fkRectLayerOutputEmbed_injective

/--
[fkRectLayerEdgeEndpoints_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectLayerEdgeEndpoints_ne_eq
  {W : Nat}
  {evenRow : Bool}
  {a : Bool × Fin W}
-- given
  (hW : 0 < W) :
-- imply
  (fkRectLayerEdgeEndpoints hW evenRow a).1 ≠ (fkRectLayerEdgeEndpoints hW evenRow a).2 := by
-- proof
  apply StatMech.FrontierD.fkRectLayerEdgeEndpoints_ne hW evenRow a

/--
[fkRectBoundaryLayerOutput_eq_finiteBoundaryConnectivityGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryLayerOutput_eq_finiteBoundaryConnectivityGraph_eq
  {W : Nat}
  {evenRow : Bool}
  {state : FKRectBoundaryState W}
-- given
  (hW : 0 < W)
  (eta : Bool × Fin W -> Bool) :
-- imply
  fkRectBoundaryLayerOutput hW evenRow state eta = finiteBoundaryConnectivityGraph (fkRectBoundaryLayerGraph hW evenRow state eta) fkRectLayerOutputEmbed := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryLayerOutput_eq_finiteBoundaryConnectivityGraph hW evenRow state eta

/--
[finiteBoundaryConnectivityGraph_isConnectivity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma finiteBoundaryConnectivityGraph_isConnectivity_eq
  {G : SimpleGraph V}
-- given
  (embed : B -> V) :
-- imply
  ∀ u v, (finiteBoundaryConnectivityGraph G embed).Adj u v ↔ u ≠ v ∧ (finiteBoundaryConnectivityGraph G embed).Reachable u v := by
-- proof
  apply StatMech.FrontierD.finiteBoundaryConnectivityGraph_isConnectivity G embed

/--
[fkRectBoundaryLayerOutput_isConnectivity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryLayerOutput_isConnectivity_eq
  {W : Nat}
  {evenRow : Bool}
  {state : FKRectBoundaryState W}
-- given
  (hW : 0 < W)
  (eta : Bool × Fin W -> Bool) :
-- imply
  (fkRectBoundaryLayerOutput hW evenRow state eta).IsConnectivity := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryLayerOutput_isConnectivity hW evenRow state eta

/--
[fkRectBoundaryLayer_component_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryLayer_component_count_eq
  {W : Nat}
  {evenRow : Bool}
  {state : FKRectBoundaryState W}
-- given
  (hW : 0 < W)
  (eta : Bool × Fin W -> Bool) :
-- imply
  Fintype.card (fkRectBoundaryLayerGraph hW evenRow state eta).ConnectedComponent = fkRectBoundaryLayerClosedCount hW evenRow state eta + Fintype.card (fkRectBoundaryLayerOutput hW evenRow state eta).ConnectedComponent := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryLayer_component_count hW evenRow state eta

/--
[fkRectLayerCollapse_inputEmbed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectLayerCollapse_inputEmbed_eq
  {W : Nat}
  {u : Bool × Fin W} :
-- imply
  fkRectLayerCollapse (fkRectLayerInputEmbed u) = u := by
-- proof
  apply StatMech.FrontierD.fkRectLayerCollapse_inputEmbed u

/--
[fkRectLayerCollapse_outputEmbed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectLayerCollapse_outputEmbed_eq
  {W : Nat}
  {u : Bool × Fin W} :
-- imply
  fkRectLayerCollapse (fkRectLayerOutputEmbed u) = u := by
-- proof
  apply StatMech.FrontierD.fkRectLayerCollapse_outputEmbed u

/--
[fkRectBoundaryVerticalLayer_adj_collapse_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryVerticalLayer_adj_collapse_reachable_eq
  {W : Nat}
  {evenRow : Bool}
  {state : FKRectBoundaryState W}
  {u v : FKRectLayerVertex W}
-- given
  (hW : 0 < W)
  (huv : (fkRectBoundaryLayerGraph hW evenRow state fkRectBoundaryVerticalLayer).Adj u v) :
-- imply
  state.Reachable (fkRectLayerCollapse u) (fkRectLayerCollapse v) := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryVerticalLayer_adj_collapse_reachable hW evenRow state huv

/--
[fkRectBoundaryVerticalLayer_reachable_collapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryVerticalLayer_reachable_collapse_eq
  {W : Nat}
  {evenRow : Bool}
  {state : FKRectBoundaryState W}
  {u v : FKRectLayerVertex W}
-- given
  (hW : 0 < W)
  (huv : (fkRectBoundaryLayerGraph hW evenRow state fkRectBoundaryVerticalLayer).Reachable u v) :
-- imply
  state.Reachable (fkRectLayerCollapse u) (fkRectLayerCollapse v) := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryVerticalLayer_reachable_collapse hW evenRow state huv

/--
[fkRectBoundaryVerticalLayer_input_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryVerticalLayer_input_reachable_eq
  {W : Nat}
  {evenRow : Bool}
  {state : FKRectBoundaryState W}
  {u v : Bool × Fin W}
-- given
  (hW : 0 < W)
  (huv : state.Reachable u v) :
-- imply
  (fkRectBoundaryLayerGraph hW evenRow state fkRectBoundaryVerticalLayer).Reachable (fkRectLayerInputEmbed u) (fkRectLayerInputEmbed v) := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryVerticalLayer_input_reachable hW evenRow state huv

/--
[fkRectBoundaryVerticalLayer_input_output_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryVerticalLayer_input_output_reachable_eq
  {W : Nat}
  {evenRow : Bool}
  {state : FKRectBoundaryState W}
  {u : Bool × Fin W}
-- given
  (hW : 0 < W) :
-- imply
  (fkRectBoundaryLayerGraph hW evenRow state fkRectBoundaryVerticalLayer).Reachable (fkRectLayerInputEmbed u) (fkRectLayerOutputEmbed u) := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryVerticalLayer_input_output_reachable hW evenRow state u

/--
[fkRectBoundaryVerticalLayer_output_reachable_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryVerticalLayer_output_reachable_iff_eq
  {W : Nat}
  {evenRow : Bool}
  {state : FKRectBoundaryState W}
  {u v : Bool × Fin W}
-- given
  (hW : 0 < W) :
-- imply
  (fkRectBoundaryLayerGraph hW evenRow state fkRectBoundaryVerticalLayer).Reachable (fkRectLayerOutputEmbed u) (fkRectLayerOutputEmbed v) ↔ state.Reachable u v := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryVerticalLayer_output_reachable_iff hW evenRow state u v

/--
[fkRectBoundaryLayerOutput_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryLayerOutput_vertical_eq
  {W : Nat}
  {evenRow : Bool}
  {state : FKRectBoundaryState W}
-- given
  (hW : 0 < W)
  (hstate : state.IsConnectivity) :
-- imply
  fkRectBoundaryLayerOutput hW evenRow state fkRectBoundaryVerticalLayer = state := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryLayerOutput_vertical hW evenRow state hstate

/--
[fkRectBoundaryLayerGraph_eq_edgeRun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryLayerGraph_eq_edgeRun_eq
  {W : Nat}
  {evenRow : Bool}
  {state : FKRectBoundaryState W}
-- given
  (hW : 0 < W)
  (eta : Bool × Fin W -> Bool) :
-- imply
  fkRectBoundaryLayerGraph hW evenRow state eta = finiteBoundaryEdgeRun id (fkRectBoundaryLayerGraph hW evenRow state (fun _ => false)) (fkRectBoundaryOpenLayerEdges hW evenRow eta) := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryLayerGraph_eq_edgeRun hW evenRow state eta

/--
[fkRectBoundaryEmptyLayer_new_reachable_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryEmptyLayer_new_reachable_iff_eq
  {W : Nat}
  {evenRow : Bool}
  {state : FKRectBoundaryState W}
  {x : Fin W}
  {v : FKRectLayerVertex W}
-- given
  (hW : 0 < W) :
-- imply
  (fkRectBoundaryLayerGraph hW evenRow state fkRectBoundaryEmptyLayer).Reachable (fkRectLayerNewRole, x) v ↔ v = (fkRectLayerNewRole, x) := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryEmptyLayer_new_reachable_iff hW evenRow state x v

/--
[fkRectBoundaryEmptyLayer_input_reachable_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryEmptyLayer_input_reachable_iff_eq
  {W : Nat}
  {evenRow : Bool}
  {state : FKRectBoundaryState W}
  {u v : Bool × Fin W}
-- given
  (hW : 0 < W) :
-- imply
  (fkRectBoundaryLayerGraph hW evenRow state fkRectBoundaryEmptyLayer).Reachable (fkRectLayerInputEmbed u) (fkRectLayerInputEmbed v) ↔ state.Reachable u v := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryEmptyLayer_input_reachable_iff hW evenRow state u v

/--
[fkRectBoundaryEmptyLayer_boundaryGraph_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryEmptyLayer_boundaryGraph_eq_eq
  {W : Nat}
  {evenRow : Bool}
  {state : FKRectBoundaryState W}
-- given
  (hW : 0 < W)
  (hstate : state.IsConnectivity) :
-- imply
  finiteBoundaryConnectivityGraph (fkRectBoundaryLayerGraph hW evenRow state fkRectBoundaryEmptyLayer) fkRectLayerInputEmbed = state := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryEmptyLayer_boundaryGraph_eq hW evenRow state hstate

/--
[fkRectBoundaryEmptyLayer_component_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryEmptyLayer_component_count_eq
  {W : Nat}
  {evenRow : Bool}
  {state : FKRectBoundaryState W}
-- given
  (hW : 0 < W)
  (hstate : state.IsConnectivity) :
-- imply
  Fintype.card (fkRectBoundaryLayerGraph hW evenRow state fkRectBoundaryEmptyLayer).ConnectedComponent = Fintype.card state.ConnectedComponent + W := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryEmptyLayer_component_count hW evenRow state hstate

/--
[fkRectStripBoundary_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectStripBoundary_false_eq
  {W : Nat}
  {n : Nat}
  {x : Fin W} :
-- imply
  fkRectStripBoundary n (false, x) = fkRectStripInitial n x := by
-- proof
  apply StatMech.FrontierD.fkRectStripBoundary_false n x

/--
[fkRectStripBoundary_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectStripBoundary_true_eq
  {W : Nat}
  {n : Nat}
  {x : Fin W} :
-- imply
  fkRectStripBoundary n (true, x) = fkRectStripCurrent n x := by
-- proof
  apply StatMech.FrontierD.fkRectStripBoundary_true n x

/--
[fkRectStripLayerEmbed_initial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectStripLayerEmbed_initial_eq
  {W : Nat}
  {n : Nat}
  {x : Fin W} :
-- imply
  fkRectStripLayerEmbed n (fkRectLayerInitialRole, x) = Sum.inl (fkRectStripInitial n x) := by
-- proof
  apply StatMech.FrontierD.fkRectStripLayerEmbed_initial n x

/--
[fkRectStripLayerEmbed_old](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectStripLayerEmbed_old_eq
  {W : Nat}
  {n : Nat}
  {x : Fin W} :
-- imply
  fkRectStripLayerEmbed n (fkRectLayerOldRole, x) = Sum.inl (fkRectStripCurrent n x) := by
-- proof
  apply StatMech.FrontierD.fkRectStripLayerEmbed_old n x

/--
[fkRectStripLayerEmbed_new](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectStripLayerEmbed_new_eq
  {W : Nat}
  {n : Nat}
  {x : Fin W} :
-- imply
  fkRectStripLayerEmbed n (fkRectLayerNewRole, x) = Sum.inr x := by
-- proof
  apply StatMech.FrontierD.fkRectStripLayerEmbed_new n x

/--
[fkRectStripLayerEmbed_input](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectStripLayerEmbed_input_eq
  {W : Nat}
  {n : Nat}
  {u : Bool × Fin W} :
-- imply
  fkRectStripLayerEmbed n (fkRectLayerInputEmbed u) = Sum.inl (fkRectStripBoundary n u) := by
-- proof
  apply StatMech.FrontierD.fkRectStripLayerEmbed_input n u

/--
[fkRectStripLayerEmbed_output](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectStripLayerEmbed_output_eq
  {W : Nat}
  {n : Nat}
  {u : Bool × Fin W} :
-- imply
  fkRectStripLayerEmbed n (fkRectLayerOutputEmbed u) = fkRectStripBoundary (n + 1) u := by
-- proof
  apply StatMech.FrontierD.fkRectStripLayerEmbed_output n u

/--
[fkRectStripGraph_succ_adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectStripGraph_succ_adj_iff_eq
  {W : Nat}
  {n : Nat}
  {u v : FKRectStripVertex W (n + 1)}
-- given
  (hW : 0 < W)
  (layers : Fin (n + 1) -> Bool × (Bool × Fin W -> Bool)) :
-- imply
  (fkRectStripGraph hW (n + 1) layers).Adj u v ↔ ((fkRectStripGraph hW n (fun i => layers i.castSucc)).sum (⊥ : SimpleGraph (Fin W))).Adj u v ∨ ∃ a : Bool × Fin W, (layers (Fin.last n)).2 a = true ∧ (SimpleGraph.edge (fkRectStripLayerEmbed n (fkRectLayerEdgeEndpoints hW (layers (Fin.last n)).1 a).1) (fkRectStripLayerEmbed n (fkRectLayerEdgeEndpoints hW (layers (Fin.last n)).1 a).2)).Adj u v := by
-- proof
  apply StatMech.FrontierD.fkRectStripGraph_succ_adj_iff hW n layers u v

/--
[fkRectOpenEdgeCount_eq_sum_layerOpenCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectOpenEdgeCount_eq_sum_layerOpenCount_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectOpenEdgeCount R omega = ∑ y : Fin R.height, fkRectBoundaryLayerOpenCount (fkRectConfigurationLayer R omega y) := by
-- proof
  apply StatMech.FrontierD.fkRectOpenEdgeCount_eq_sum_layerOpenCount R omega

/--
[fkRectBoundaryRunWeight_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryRunWeight_eq_eq
  {W : Nat}
  {q : Real}
  {state : FKRectBoundaryState W}
-- given
  (hW : 0 < W)
  (layers : List (Bool × (Bool × Fin W -> Bool))) :
-- imply
  fkRectBoundaryRunWeight hW q state layers = Real.sqrt q ^ fkRectBoundaryRunOpenCount layers * q ^ fkRectBoundaryRunClosedCount hW state layers := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryRunWeight_eq hW q state layers

/--
[fkRectBoundaryRunOpenCount_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryRunOpenCount_eq_sum_eq
  {W : Nat}
-- given
  (layers : List (Bool × (Bool × Fin W -> Bool))) :
-- imply
  fkRectBoundaryRunOpenCount layers = (layers.map fun layer => fkRectBoundaryLayerOpenCount layer.2).sum := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryRunOpenCount_eq_sum layers

/--
[fkRectBoundaryNonSeamRow_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryNonSeamRow_val_eq
  {R : FKRectTorus}
  {i : Fin (R.height - 1)} :
-- imply
  (fkRectBoundaryNonSeamRow R i).val = i.val + 1 := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryNonSeamRow_val R i

/--
[fkRect_sum_rows_eq_seam_add_nonSeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRect_sum_rows_eq_seam_add_nonSeam_eq
  {R : FKRectTorus}
-- given
  (f : Fin R.height -> Nat) :
-- imply
  (∑ y, f y) = f (fkRectBoundarySeamRow R) + ∑ i : Fin (R.height - 1), f (fkRectBoundaryNonSeamRow R i) := by
-- proof
  apply StatMech.FrontierD.fkRect_sum_rows_eq_seam_add_nonSeam R f

/--
[fkRectOpenEdgeCount_eq_run_add_seam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectOpenEdgeCount_eq_run_add_seam_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectOpenEdgeCount R omega = fkRectBoundaryRunOpenCount (fkRectConfigurationNonSeamLayers R omega) + fkRectBoundaryLayerOpenCount (fkRectConfigurationLayer R omega (fkRectBoundarySeamRow R)) := by
-- proof
  apply StatMech.FrontierD.fkRectOpenEdgeCount_eq_run_add_seam R omega

/--
[fkRectBoundaryInitialState_reachable_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryInitialState_reachable_iff_eq
  {W : Nat}
  {u v : Bool × Fin W} :
-- imply
  (fkRectBoundaryInitialState W).Reachable u v ↔ u.2 = v.2 := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryInitialState_reachable_iff W u v

/--
[fkRectBoundaryInitialState_isConnectivity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryInitialState_isConnectivity_eq
  {W : Nat} :
-- imply
  (fkRectBoundaryInitialState W).IsConnectivity := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryInitialState_isConnectivity W

/--
[simpleGraph_sum_reachable_inl_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma simpleGraph_sum_reachable_inl_iff_eq
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  {u v : V} :
-- imply
  (G.sum H).Reachable (Sum.inl u) (Sum.inl v) ↔ G.Reachable u v := by
-- proof
  apply StatMech.FrontierD.simpleGraph_sum_reachable_inl_iff

/--
[simpleGraph_sum_reachable_inr_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma simpleGraph_sum_reachable_inr_iff_eq
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  {u v : W} :
-- imply
  (G.sum H).Reachable (Sum.inr u) (Sum.inr v) ↔ H.Reachable u v := by
-- proof
  apply StatMech.FrontierD.simpleGraph_sum_reachable_inr_iff

/--
[simpleGraph_sum_not_reachable_inl_inr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma simpleGraph_sum_not_reachable_inl_inr_eq
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  {u : V}
  {v : W} :
-- imply
  ¬(G.sum H).Reachable (Sum.inl u) (Sum.inr v) := by
-- proof
  apply StatMech.FrontierD.simpleGraph_sum_not_reachable_inl_inr

/--
[simpleGraph_sum_not_reachable_inr_inl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma simpleGraph_sum_not_reachable_inr_inl_eq
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  {u : W}
  {v : V} :
-- imply
  ¬(G.sum H).Reachable (Sum.inr u) (Sum.inl v) := by
-- proof
  apply StatMech.FrontierD.simpleGraph_sum_not_reachable_inr_inl

/--
[simpleGraph_card_components_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma simpleGraph_card_components_sum_eq
  [Finite V]
  [Finite W]
  {G : SimpleGraph V}
  {H : SimpleGraph W} :
-- imply
  Nat.card (G.sum H).ConnectedComponent = Nat.card G.ConnectedComponent + Nat.card H.ConnectedComponent := by
-- proof
  apply StatMech.FrontierD.simpleGraph_card_components_sum G H

/--
[fkRectBoundaryInitialState_component_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryInitialState_component_count_eq
  {W : Nat} :
-- imply
  Nat.card (fkRectBoundaryInitialState W).ConnectedComponent = W := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryInitialState_component_count W

/--
[fkRectStripState_isConnectivity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectStripState_isConnectivity_eq
  {W : Nat}
  {n : Nat}
-- given
  (hW : 0 < W)
  (layers : Fin n -> Bool × (Bool × Fin W -> Bool)) :
-- imply
  (fkRectStripState hW n layers).IsConnectivity := by
-- proof
  apply StatMech.FrontierD.fkRectStripState_isConnectivity hW n layers

/--
[fkRectBoundaryEmptyLayer_reachable_new_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryEmptyLayer_reachable_new_iff_eq
  {W : Nat}
  {evenRow : Bool}
  {state : FKRectBoundaryState W}
  {v : FKRectLayerVertex W}
  {x : Fin W}
-- given
  (hW : 0 < W) :
-- imply
  (fkRectBoundaryLayerGraph hW evenRow state fkRectBoundaryEmptyLayer).Reachable v (fkRectLayerNewRole, x) ↔ v = (fkRectLayerNewRole, x) := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryEmptyLayer_reachable_new_iff hW evenRow state v x

/--
[fkRectStripExpanded_reachable_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectStripExpanded_reachable_iff_eq
  {W : Nat}
  {n : Nat}
  {evenRow : Bool}
  {u v : FKRectLayerVertex W}
-- given
  (hW : 0 < W)
  (layers : Fin n -> Bool × (Bool × Fin W -> Bool))
  (hprev : ∀ u v : Bool × Fin W, ((fkRectStripGraph hW n layers).Reachable (fkRectStripBoundary n u) (fkRectStripBoundary n v) ↔ (fkRectStripState hW n layers).Reachable u v)) :
-- imply
  ((fkRectStripGraph hW n layers).sum (⊥ : SimpleGraph (Fin W))).Reachable (fkRectStripLayerEmbed n u) (fkRectStripLayerEmbed n v) ↔ (fkRectBoundaryLayerGraph hW evenRow (fkRectStripState hW n layers) fkRectBoundaryEmptyLayer).Reachable u v := by
-- proof
  apply StatMech.FrontierD.fkRectStripExpanded_reachable_iff hW n layers evenRow hprev u v

/--
[fkRectStrip_boundary_reachable_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectStrip_boundary_reachable_iff_eq
  {W : Nat}
  {n : Nat}
  {u v : Bool × Fin W}
-- given
  (hW : 0 < W)
  (layers : Fin n -> Bool × (Bool × Fin W -> Bool)) :
-- imply
  (fkRectStripGraph hW n layers).Reachable (fkRectStripBoundary n u) (fkRectStripBoundary n v) ↔ (fkRectStripState hW n layers).Reachable u v := by
-- proof
  apply StatMech.FrontierD.fkRectStrip_boundary_reachable_iff hW n layers u v

/--
[fkRectStrip_component_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectStrip_component_count_eq
  {W : Nat}
  {n : Nat}
-- given
  (hW : 0 < W)
  (layers : Fin n -> Bool × (Bool × Fin W -> Bool)) :
-- imply
  Nat.card (fkRectStripGraph hW n layers).ConnectedComponent = fkRectStripClosedCount hW n layers + Nat.card (fkRectStripState hW n layers).ConnectedComponent := by
-- proof
  apply StatMech.FrontierD.fkRectStrip_component_count hW n layers

/--
[fkRectBoundaryRunState_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryRunState_append_eq
  {W : Nat}
  {state : FKRectBoundaryState W}
-- given
  (hW : 0 < W)
  (left right : List (Bool × (Bool × Fin W -> Bool))) :
-- imply
  fkRectBoundaryRunState hW state (left ++ right) = fkRectBoundaryRunState hW (fkRectBoundaryRunState hW state left) right := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryRunState_append hW state left right

/--
[fkRectBoundaryRunClosedCount_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryRunClosedCount_append_eq
  {W : Nat}
  {state : FKRectBoundaryState W}
-- given
  (hW : 0 < W)
  (left right : List (Bool × (Bool × Fin W -> Bool))) :
-- imply
  fkRectBoundaryRunClosedCount hW state (left ++ right) = fkRectBoundaryRunClosedCount hW state left + fkRectBoundaryRunClosedCount hW (fkRectBoundaryRunState hW state left) right := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryRunClosedCount_append hW state left right

/--
[fkRectStripState_eq_runState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectStripState_eq_runState_eq
  {W : Nat}
  {n : Nat}
-- given
  (hW : 0 < W)
  (layers : Fin n -> Bool × (Bool × Fin W -> Bool)) :
-- imply
  fkRectStripState hW n layers = fkRectBoundaryRunState hW (fkRectBoundaryInitialState W) (List.ofFn layers) := by
-- proof
  apply StatMech.FrontierD.fkRectStripState_eq_runState hW n layers

/--
[fkRectStripClosedCount_eq_runClosedCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectStripClosedCount_eq_runClosedCount_eq
  {W : Nat}
  {n : Nat}
-- given
  (hW : 0 < W)
  (layers : Fin n -> Bool × (Bool × Fin W -> Bool)) :
-- imply
  fkRectStripClosedCount hW n layers = fkRectBoundaryRunClosedCount hW (fkRectBoundaryInitialState W) (List.ofFn layers) := by
-- proof
  apply StatMech.FrontierD.fkRectStripClosedCount_eq_runClosedCount hW n layers

/--
[fkRectStripVertexEquiv_inl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectStripVertexEquiv_inl_eq
  {W n : Nat}
  {v : FKRectStripVertex W n} :
-- imply
  fkRectStripVertexEquiv W (n + 1) (Sum.inl v) = ((fkRectStripVertexEquiv W n v).1, (fkRectStripVertexEquiv W n v).2.castSucc) := by
-- proof
  apply StatMech.FrontierD.fkRectStripVertexEquiv_inl v

/--
[fkRectStripVertexEquiv_inr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectStripVertexEquiv_inr_eq
  {W n : Nat}
  {x : Fin W} :
-- imply
  fkRectStripVertexEquiv W (n + 1) (Sum.inr x) = (x, Fin.last (n + 1)) := by
-- proof
  apply StatMech.FrontierD.fkRectStripVertexEquiv_inr x

/--
[fkRectStripVertexEquiv_initial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectStripVertexEquiv_initial_eq
  {W : Nat}
  {n : Nat}
  {x : Fin W} :
-- imply
  fkRectStripVertexEquiv W n (fkRectStripInitial n x) = (x, 0) := by
-- proof
  apply StatMech.FrontierD.fkRectStripVertexEquiv_initial n x

/--
[fkRectStripVertexEquiv_current](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectStripVertexEquiv_current_eq
  {W : Nat}
  {n : Nat}
  {x : Fin W} :
-- imply
  fkRectStripVertexEquiv W n (fkRectStripCurrent n x) = (x, Fin.last n) := by
-- proof
  apply StatMech.FrontierD.fkRectStripVertexEquiv_current n x

/--
[fkRectStripVertexEquiv_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectStripVertexEquiv_boundary_eq
  {W : Nat}
  {n : Nat}
  {u : Bool × Fin W} :
-- imply
  fkRectStripVertexEquiv W n (fkRectStripBoundary n u) = if u.1 then (u.2, Fin.last n) else (u.2, 0) := by
-- proof
  apply StatMech.FrontierD.fkRectStripVertexEquiv_boundary n u

/--
[fkRectCoordinateLayerEdgeEndpoints_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectCoordinateLayerEdgeEndpoints_last_eq
  {W : Nat}
  {n : Nat}
  {evenRow : Bool}
  {a : Bool × Fin W}
-- given
  (hW : 0 < W) :
-- imply
  Prod.map (fkRectStripVertexEquiv W (n + 1)) (fkRectStripVertexEquiv W (n + 1)) (Prod.map (fkRectStripLayerEmbed n) (fkRectStripLayerEmbed n) (fkRectLayerEdgeEndpoints hW evenRow a)) = fkRectCoordinateLayerEdgeEndpoints hW (Fin.last n) evenRow a := by
-- proof
  apply StatMech.FrontierD.fkRectCoordinateLayerEdgeEndpoints_last hW n evenRow a

/--
[fin_exists_castSucc_or_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fin_exists_castSucc_or_last_eq
  {n : Nat}
  {P : Fin (n + 1) -> Prop} :
-- imply
  (∃ i, P i) ↔ (∃ i : Fin n, P i.castSucc) ∨ P (Fin.last n) := by
-- proof
  apply StatMech.FrontierD.fin_exists_castSucc_or_last

/--
[fkRectCoordinateLayerEdge_castSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectCoordinateLayerEdge_castSucc_eq
  {W n : Nat}
  {i : Fin n}
  {evenRow : Bool}
  {a : Bool × Fin W}
-- given
  (hW : 0 < W) :
-- imply
  fkRectCoordinateLayerEdge hW i.castSucc evenRow a = Sym2.map (fun z : Fin W × Fin (n + 1) => (z.1, z.2.castSucc)) (fkRectCoordinateLayerEdge hW i evenRow a) := by
-- proof
  apply StatMech.FrontierD.fkRectCoordinateLayerEdge_castSucc hW i evenRow a

/--
[fkRectCoordinateLayerEdge_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectCoordinateLayerEdge_last_eq
  {W : Nat}
  {n : Nat}
  {evenRow : Bool}
  {a : Bool × Fin W}
-- given
  (hW : 0 < W) :
-- imply
  fkRectCoordinateLayerEdge hW (Fin.last n) evenRow a = Sym2.map (fkRectStripVertexEquiv W (n + 1)) s(fkRectStripLayerEmbed n (fkRectLayerEdgeEndpoints hW evenRow a).1, fkRectStripLayerEmbed n (fkRectLayerEdgeEndpoints hW evenRow a).2) := by
-- proof
  apply StatMech.FrontierD.fkRectCoordinateLayerEdge_last hW n evenRow a

/--
[sym2_map_eq_map_iff_of_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma sym2_map_eq_map_iff_of_injective_eq
  {e e' : Sym2 A}
-- given
  (f : A -> B)
  (hf : Function.Injective f) :
-- imply
  Sym2.map f e = Sym2.map f e' ↔ e = e' := by
-- proof
  apply StatMech.FrontierD.sym2_map_eq_map_iff_of_injective f hf e e'

/--
[fkRectStripRowCast_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectStripRowCast_injective_eq
  {W n : Nat} :
-- imply
  Function.Injective (fkRectStripRowCast (W := W) (n := n)) := by
-- proof
  apply StatMech.FrontierD.fkRectStripRowCast_injective

/--
[sym2_fkRectStripRowCast_ne_cast_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma sym2_fkRectStripRowCast_ne_cast_last_eq
  {W n : Nat}
  {e : Sym2 (Fin W × Fin (n + 1))}
  {z : Fin W × Fin (n + 1)}
  {x : Fin W} :
-- imply
  Sym2.map fkRectStripRowCast e ≠ s(fkRectStripRowCast z, (x, Fin.last (n + 1))) := by
-- proof
  apply StatMech.FrontierD.sym2_fkRectStripRowCast_ne_cast_last e z x

/--
[sym2_fkRectStripRowCast_ne_last_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma sym2_fkRectStripRowCast_ne_last_last_eq
  {W n : Nat}
  {e : Sym2 (Fin W × Fin (n + 1))}
  {x y : Fin W} :
-- imply
  Sym2.map fkRectStripRowCast e ≠ s((x, Fin.last (n + 1)), (y, Fin.last (n + 1))) := by
-- proof
  apply StatMech.FrontierD.sym2_fkRectStripRowCast_ne_last_last e x y

/--
[fkRectStripGraph_adj_iff_coordinateEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectStripGraph_adj_iff_coordinateEdge_eq
  {W : Nat}
  {n : Nat}
  {u v : FKRectStripVertex W n}
-- given
  (hW : 0 < W)
  (layers : Fin n -> Bool × (Bool × Fin W -> Bool)) :
-- imply
  (fkRectStripGraph hW n layers).Adj u v ↔ u ≠ v ∧ ∃ i : Fin n, ∃ a : Bool × Fin W, (layers i).2 a = true ∧ fkRectCoordinateLayerEdge hW i (layers i).1 a = s(fkRectStripVertexEquiv W n u, fkRectStripVertexEquiv W n v) := by
-- proof
  apply StatMech.FrontierD.fkRectStripGraph_adj_iff_coordinateEdge hW n layers u v

/--
[fkRectBoundarySeamEdgeEndpoints_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundarySeamEdgeEndpoints_ne_eq
  {W : Nat}
  {a : Bool × Fin W}
-- given
  (hW : 0 < W) :
-- imply
  (fkRectBoundarySeamEdgeEndpoints hW a).1 ≠ (fkRectBoundarySeamEdgeEndpoints hW a).2 := by
-- proof
  apply StatMech.FrontierD.fkRectBoundarySeamEdgeEndpoints_ne hW a

/--
[fkRectBoundarySeamGraph_eq_edgeRun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundarySeamGraph_eq_edgeRun_eq
  {W : Nat}
  {state : FKRectBoundaryState W}
-- given
  (hW : 0 < W)
  (eta : Bool × Fin W -> Bool) :
-- imply
  fkRectBoundarySeamGraph hW state eta = finiteBoundaryEdgeRun id state (fkRectBoundaryOpenSeamEdges hW eta) := by
-- proof
  apply StatMech.FrontierD.fkRectBoundarySeamGraph_eq_edgeRun hW state eta

/--
[fkRectCoordinateSeamEdge_eq_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectCoordinateSeamEdge_eq_map_eq
  {W : Nat}
  {n : Nat}
  {a : Bool × Fin W}
-- given
  (hW : 0 < W) :
-- imply
  fkRectCoordinateSeamEdge (n := n) hW a = Sym2.map (fkRectStripVertexEquiv W n) s(fkRectStripBoundary n (fkRectBoundarySeamEdgeEndpoints hW a).1, fkRectStripBoundary n (fkRectBoundarySeamEdgeEndpoints hW a).2) := by
-- proof
  apply StatMech.FrontierD.fkRectCoordinateSeamEdge_eq_map hW n a

/--
[fkRectStripSeamGraph_adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectStripSeamGraph_adj_iff_eq
  {W : Nat}
  {n : Nat}
  {u v : FKRectStripVertex W n}
-- given
  (hW : 0 < W)
  (layers : Fin n -> Bool × (Bool × Fin W -> Bool))
  (eta : Bool × Fin W -> Bool) :
-- imply
  (fkRectStripSeamGraph hW n layers eta).Adj u v ↔ (fkRectStripGraph hW n layers).Adj u v ∨ ∃ a : Bool × Fin W, eta a = true ∧ (SimpleGraph.edge (fkRectStripBoundary n (fkRectBoundarySeamEdgeEndpoints hW a).1) (fkRectStripBoundary n (fkRectBoundarySeamEdgeEndpoints hW a).2)).Adj u v := by
-- proof
  apply StatMech.FrontierD.fkRectStripSeamGraph_adj_iff hW n layers eta u v

/--
[fkRectStripSeamGraph_adj_iff_coordinateEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectStripSeamGraph_adj_iff_coordinateEdge_eq
  {W : Nat}
  {n : Nat}
  {u v : FKRectStripVertex W n}
-- given
  (hW : 0 < W)
  (layers : Fin n -> Bool × (Bool × Fin W -> Bool))
  (eta : Bool × Fin W -> Bool) :
-- imply
  (fkRectStripSeamGraph hW n layers eta).Adj u v ↔ u ≠ v ∧ ((∃ i : Fin n, ∃ a : Bool × Fin W, (layers i).2 a = true ∧ fkRectCoordinateLayerEdge hW i (layers i).1 a = s(fkRectStripVertexEquiv W n u, fkRectStripVertexEquiv W n v)) ∨ ∃ a : Bool × Fin W, eta a = true ∧ fkRectCoordinateSeamEdge (n := n) hW a = s(fkRectStripVertexEquiv W n u, fkRectStripVertexEquiv W n v)) := by
-- proof
  apply StatMech.FrontierD.fkRectStripSeamGraph_adj_iff_coordinateEdge hW n layers eta u v

/--
[fkRectStripSeamGraph_component_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectStripSeamGraph_component_count_eq
  {W : Nat}
  {n : Nat}
-- given
  (hW : 0 < W)
  (layers : Fin n -> Bool × (Bool × Fin W -> Bool))
  (eta : Bool × Fin W -> Bool) :
-- imply
  Nat.card (fkRectStripSeamGraph hW n layers eta).ConnectedComponent = fkRectStripClosedCount hW n layers + Nat.card (fkRectBoundarySeamGraph hW (fkRectStripState hW n layers) eta).ConnectedComponent := by
-- proof
  apply StatMech.FrontierD.fkRectStripSeamGraph_component_count hW n layers eta

/--
[fkRectBoundaryTransferCoefficient_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryTransferCoefficient_eq_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : R.Configuration} :
-- imply
  fkRectBoundaryTransferCoefficient R q omega = Real.sqrt q ^ fkRectOpenEdgeCount R omega * q ^ fkRectBoundaryTransferClusterCount R omega := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryTransferCoefficient_eq R q omega

/--
[fkRectConfigurationNonSeamLayers_eq_ofFn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectConfigurationNonSeamLayers_eq_ofFn_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectConfigurationNonSeamLayers R omega = List.ofFn (fkRectConfigurationNonSeamLayerFn R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectConfigurationNonSeamLayers_eq_ofFn R omega

/--
[fkRectConfigurationScheduleEquiv_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectConfigurationScheduleEquiv_fst_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  (fkRectConfigurationScheduleEquiv R omega).1 = fkRectConfigurationLayer R omega (fkRectBoundarySeamRow R) := by
-- proof
  apply StatMech.FrontierD.fkRectConfigurationScheduleEquiv_fst R omega

/--
[fkRectConfigurationScheduleEquiv_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectConfigurationScheduleEquiv_snd_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {i : Fin (R.height - 1)} :
-- imply
  (fkRectConfigurationScheduleEquiv R omega).2 i = fkRectConfigurationLayer R omega (fkRectBoundaryNonSeamRow R i) := by
-- proof
  apply StatMech.FrontierD.fkRectConfigurationScheduleEquiv_snd R omega i

/--
[fkRectConfigurationScheduleEquiv_symm_seam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectConfigurationScheduleEquiv_symm_seam_eq
  {R : FKRectTorus}
-- given
  (seam : Bool × Fin R.width -> Bool)
  (layers : Fin (R.height - 1) -> Bool × Fin R.width -> Bool) :
-- imply
  fkRectConfigurationLayer R ((fkRectConfigurationScheduleEquiv R).symm (seam, layers)) (fkRectBoundarySeamRow R) = seam := by
-- proof
  apply StatMech.FrontierD.fkRectConfigurationScheduleEquiv_symm_seam R seam layers

/--
[fkRectConfigurationScheduleEquiv_symm_nonSeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectConfigurationScheduleEquiv_symm_nonSeam_eq
  {R : FKRectTorus}
  {i : Fin (R.height - 1)}
-- given
  (seam : Bool × Fin R.width -> Bool)
  (layers : Fin (R.height - 1) -> Bool × Fin R.width -> Bool) :
-- imply
  fkRectConfigurationLayer R ((fkRectConfigurationScheduleEquiv R).symm (seam, layers)) (fkRectBoundaryNonSeamRow R i) = layers i := by
-- proof
  apply StatMech.FrontierD.fkRectConfigurationScheduleEquiv_symm_nonSeam R seam layers i

/--
[fkRectBoundaryTransferCoefficient_schedule_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryTransferCoefficient_schedule_symm_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (seam : Bool × Fin R.width -> Bool)
  (layers : Fin (R.height - 1) -> Bool × Fin R.width -> Bool) :
-- imply
  fkRectBoundaryTransferCoefficient R q ((fkRectConfigurationScheduleEquiv R).symm (seam, layers)) = fkRectBoundaryRunWeight R.width_pos q (fkRectBoundaryInitialState R.width) (List.ofFn fun i : Fin (R.height - 1) => (decide (Even (fkRectBoundaryNonSeamRow R i).val), layers i)) * fkRectBoundarySeamWeight R.width_pos q (fkRectBoundaryRunState R.width_pos (fkRectBoundaryInitialState R.width) (List.ofFn fun i : Fin (R.height - 1) => (decide (Even (fkRectBoundaryNonSeamRow R i).val), layers i))) seam := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryTransferCoefficient_schedule_symm R q seam layers

/--
[sum_fkRectBoundaryTransferCoefficient_eq_layerSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma sum_fkRectBoundaryTransferCoefficient_eq_layerSum_eq
  {R : FKRectTorus}
  {q : Real} :
-- imply
  (∑ omega : R.Configuration, fkRectBoundaryTransferCoefficient R q omega) = ∑ layers : Fin (R.height - 1) -> Bool × Fin R.width -> Bool, fkRectBoundaryRunWeight R.width_pos q (fkRectBoundaryInitialState R.width) (List.ofFn fun i : Fin (R.height - 1) => (decide (Even (fkRectBoundaryNonSeamRow R i).val), layers i)) * fkRectBoundarySeamFunctional R.width_pos q (fkRectBoundaryRunState R.width_pos (fkRectBoundaryInitialState R.width) (List.ofFn fun i : Fin (R.height - 1) => (decide (Even (fkRectBoundaryNonSeamRow R i).val), layers i))) := by
-- proof
  apply StatMech.FrontierD.sum_fkRectBoundaryTransferCoefficient_eq_layerSum R q

/--
[finFunctionConsEquiv_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma finFunctionConsEquiv_fst_eq
  {n : Nat}
-- given
  (f : Fin (n + 1) -> A) :
-- imply
  (finFunctionConsEquiv n A f).1 = f 0 := by
-- proof
  apply StatMech.FrontierD.finFunctionConsEquiv_fst f

/--
[finFunctionConsEquiv_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma finFunctionConsEquiv_snd_eq
  {n : Nat}
  {i : Fin n}
-- given
  (f : Fin (n + 1) -> A) :
-- imply
  (finFunctionConsEquiv n A f).2 i = f i.succ := by
-- proof
  apply StatMech.FrontierD.finFunctionConsEquiv_snd f i

/--
[finFunctionConsEquiv_symm_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma finFunctionConsEquiv_symm_zero_eq
  {n : Nat}
  {a : A}
-- given
  (f : Fin n -> A) :
-- imply
  (finFunctionConsEquiv n A).symm (a, f) 0 = a := by
-- proof
  apply StatMech.FrontierD.finFunctionConsEquiv_symm_zero a f

/--
[finFunctionConsEquiv_symm_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma finFunctionConsEquiv_symm_succ_eq
  {n : Nat}
  {a : A}
  {i : Fin n}
-- given
  (f : Fin n -> A) :
-- imply
  (finFunctionConsEquiv n A).symm (a, f) i.succ = f i := by
-- proof
  apply StatMech.FrontierD.finFunctionConsEquiv_symm_succ a f i

/--
[fkRectBoundaryFiniteLayerSum_eq_listCoefficientSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryFiniteLayerSum_eq_listCoefficientSum_eq
  {W : Nat}
  {q : Real}
  {state : FKRectBoundaryState W}
  {n : Nat}
-- given
  (hW : 0 < W)
  (parity : Fin n -> Bool) :
-- imply
  (∑ layers : Fin n -> Bool × Fin W -> Bool, fkRectBoundaryRunWeight hW q state (List.ofFn fun i : Fin n => (parity i, layers i)) * fkRectBoundarySeamFunctional hW q (fkRectBoundaryRunState hW state (List.ofFn fun i : Fin n => (parity i, layers i)))) = fkRectBoundaryListCoefficientSum hW q state (List.ofFn parity) := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryFiniteLayerSum_eq_listCoefficientSum hW q state n parity

/--
[ofFn_even_succ_eq_fkRectBoundaryAlternatingParityList](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma ofFn_even_succ_eq_fkRectBoundaryAlternatingParityList_eq
  {blocks : Nat} :
-- imply
  List.ofFn (fun i : Fin (2 * blocks + 1) => decide (Even (i.val + 1))) = fkRectBoundaryAlternatingParityList blocks := by
-- proof
  apply StatMech.FrontierD.ofFn_even_succ_eq_fkRectBoundaryAlternatingParityList blocks

/--
[fkRect_nonSeamParityList_eq_alternating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRect_nonSeamParityList_eq_alternating_eq
  {R : FKRectTorus}
  {blocks : Nat}
-- given
  (hheight : R.height = 2 * (blocks + 1)) :
-- imply
  List.ofFn (fun i : Fin (R.height - 1) => decide (Even (fkRectBoundaryNonSeamRow R i).val)) = fkRectBoundaryAlternatingParityList blocks := by
-- proof
  apply StatMech.FrontierD.fkRect_nonSeamParityList_eq_alternating R blocks hheight

/--
[fkRectStripTorusRowEquiv_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectStripTorusRowEquiv_val_eq
  {R : FKRectTorus}
  {i : Fin (R.height - 1 + 1)} :
-- imply
  (fkRectStripTorusRowEquiv R i).val = i.val := by
-- proof
  apply StatMech.FrontierD.fkRectStripTorusRowEquiv_val R i

/--
[fkRectStripTorusRowEquiv_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectStripTorusRowEquiv_succ_eq
  {R : FKRectTorus}
  {i : Fin (R.height - 1)} :
-- imply
  fkRectStripTorusRowEquiv R i.succ = fkRectBoundaryNonSeamRow R i := by
-- proof
  apply StatMech.FrontierD.fkRectStripTorusRowEquiv_succ R i

/--
[fkRectStripTorusRowEquiv_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectStripTorusRowEquiv_zero_eq
  {R : FKRectTorus} :
-- imply
  fkRectStripTorusRowEquiv R (0 : Fin (R.height - 1 + 1)) = fkRectBoundarySeamRow R := by
-- proof
  apply StatMech.FrontierD.fkRectStripTorusRowEquiv_zero R

/--
[fkRect_cyclicPred_nonSeamRow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRect_cyclicPred_nonSeamRow_eq
  {R : FKRectTorus}
  {i : Fin (R.height - 1)} :
-- imply
  SixVertexArrows.cyclicPred R.height_pos (fkRectBoundaryNonSeamRow R i) = fkRectStripTorusRowEquiv R i.castSucc := by
-- proof
  apply StatMech.FrontierD.fkRect_cyclicPred_nonSeamRow R i

/--
[fkRect_cyclicPred_seamRow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRect_cyclicPred_seamRow_eq
  {R : FKRectTorus} :
-- imply
  SixVertexArrows.cyclicPred R.height_pos (fkRectBoundarySeamRow R) = fkRectStripTorusRowEquiv R (Fin.last (R.height - 1)) := by
-- proof
  apply StatMech.FrontierD.fkRect_cyclicPred_seamRow R

/--
[fkRectCoordinateLayerEdge_map_eq_indexedEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectCoordinateLayerEdge_map_eq_indexedEdge_eq
  {R : FKRectTorus}
  {i : Fin (R.height - 1)}
  {a : Bool × Fin R.width} :
-- imply
  Sym2.map (fkRectStripCoordinateTorusEquiv R) (fkRectCoordinateLayerEdge R.width_pos i (decide (Even (fkRectBoundaryNonSeamRow R i).val)) a) = fkRectTorusIndexedEdge R (a.1, (a.2, fkRectBoundaryNonSeamRow R i)) := by
-- proof
  apply StatMech.FrontierD.fkRectCoordinateLayerEdge_map_eq_indexedEdge R i a

/--
[fkRectCoordinateSeamEdge_map_eq_indexedEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectCoordinateSeamEdge_map_eq_indexedEdge_eq
  {R : FKRectTorus}
  {a : Bool × Fin R.width} :
-- imply
  Sym2.map (fkRectStripCoordinateTorusEquiv R) (fkRectCoordinateSeamEdge (n := R.height - 1) R.width_pos a) = fkRectTorusIndexedEdge R (a.1, (a.2, fkRectBoundarySeamRow R)) := by
-- proof
  apply StatMech.FrontierD.fkRectCoordinateSeamEdge_map_eq_indexedEdge R a

/--
[fkRectOpenGraph_adj_iff_coordinateSchedule](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectOpenGraph_adj_iff_coordinateSchedule_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {u v : Fin R.width × Fin (R.height - 1 + 1)} :
-- imply
  (fkRectOpenGraph R omega).Adj (fkRectStripCoordinateTorusEquiv R u) (fkRectStripCoordinateTorusEquiv R v) ↔ u ≠ v ∧ ((∃ i : Fin (R.height - 1), ∃ a : Bool × Fin R.width, (fkRectConfigurationNonSeamLayerFn R omega i).2 a = true ∧ fkRectCoordinateLayerEdge R.width_pos i (fkRectConfigurationNonSeamLayerFn R omega i).1 a = s(u, v)) ∨ ∃ a : Bool × Fin R.width, fkRectConfigurationLayer R omega (fkRectBoundarySeamRow R) a = true ∧ fkRectCoordinateSeamEdge (n := R.height - 1) R.width_pos a = s(u, v)) := by
-- proof
  apply StatMech.FrontierD.fkRectOpenGraph_adj_iff_coordinateSchedule R omega u v

/--
[fkRectConfigurationStripSeamGraph_component_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectConfigurationStripSeamGraph_component_count_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  Fintype.card (fkRectConfigurationStripSeamGraph R omega).ConnectedComponent = fkRectBoundaryTransferClusterCount R omega := by
-- proof
  apply StatMech.FrontierD.fkRectConfigurationStripSeamGraph_component_count R omega

/--
[fkRectConfigurationStripSeamGraph_component_count_eq_numClusters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectConfigurationStripSeamGraph_component_count_eq_numClusters_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  Fintype.card (fkRectConfigurationStripSeamGraph R omega).ConnectedComponent = fkRectNumClusters R omega := by
-- proof
  apply StatMech.FrontierD.fkRectConfigurationStripSeamGraph_component_count_eq_numClusters R omega

/--
[fkRectBoundaryTransferClusterCount_eq_numClusters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryTransferClusterCount_eq_numClusters_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectBoundaryTransferClusterCount R omega = fkRectNumClusters R omega := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryTransferClusterCount_eq_numClusters R omega

/--
[fkRectBoundaryTransferCoefficient_eq_criticalReducedWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryTransferCoefficient_eq_criticalReducedWeight_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : R.Configuration} :
-- imply
  fkRectBoundaryTransferCoefficient R q omega = fkRectCriticalReducedWeight R q omega := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryTransferCoefficient_eq_criticalReducedWeight R q omega

/--
[fkRectBoundaryTransferClusterCount_eq_numClusters_of_geometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryTransferClusterCount_eq_numClusters_of_geometry_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
-- given
  (hgeometry : Fintype.card (fkRectConfigurationStripSeamGraph R omega).ConnectedComponent = fkRectNumClusters R omega) :
-- imply
  fkRectBoundaryTransferClusterCount R omega = fkRectNumClusters R omega := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryTransferClusterCount_eq_numClusters_of_geometry R omega hgeometry

/--
[fkRectBoundaryTransferCoefficient_eq_criticalReducedWeight_of_geometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryTransferCoefficient_eq_criticalReducedWeight_of_geometry_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : R.Configuration}
-- given
  (hgeometry : Fintype.card (fkRectConfigurationStripSeamGraph R omega).ConnectedComponent = fkRectNumClusters R omega) :
-- imply
  fkRectBoundaryTransferCoefficient R q omega = fkRectCriticalReducedWeight R q omega := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryTransferCoefficient_eq_criticalReducedWeight_of_geometry R q omega hgeometry

/--
[fkRectBoundaryLayerWeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryLayerWeight_pos_eq
  {W : Nat}
  {q : Real}
  {evenRow : Bool}
  {state : FKRectBoundaryState W}
-- given
  (hW : 0 < W)
  (hq : 0 < q)
  (eta : Bool × Fin W -> Bool) :
-- imply
  0 < fkRectBoundaryLayerWeight hW q evenRow state eta := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryLayerWeight_pos hW hq evenRow state eta

/--
[fkRectBoundaryLayerTransfer_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryLayerTransfer_nonneg_eq
  {W : Nat}
  {q : Real}
  {evenRow : Bool}
  {source target : FKRectBoundaryState W}
-- given
  (hW : 0 < W)
  (hq : 0 < q) :
-- imply
  0 <= fkRectBoundaryLayerTransfer hW q evenRow source target := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryLayerTransfer_nonneg hW hq evenRow source target

/--
[fkRectBoundaryLayerTransfer_target_isConnectivity_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryLayerTransfer_target_isConnectivity_of_pos_eq
  {W : Nat}
  {q : Real}
  {evenRow : Bool}
  {source target : FKRectBoundaryState W}
-- given
  (hW : 0 < W)
  (hq : 0 < q)
  (hpos : 0 < fkRectBoundaryLayerTransfer hW q evenRow source target) :
-- imply
  target.IsConnectivity := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryLayerTransfer_target_isConnectivity_of_pos hW hq evenRow source target hpos

/--
[fkRectBoundaryTwoLayerTransfer_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryTwoLayerTransfer_nonneg_eq
  {W : Nat}
  {q : Real}
  {source target : FKRectBoundaryState W}
-- given
  (hW : 0 < W)
  (hq : 0 < q) :
-- imply
  0 ≤ fkRectBoundaryTwoLayerTransfer hW q source target := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryTwoLayerTransfer_nonneg hW hq source target

/--
[fkRectBoundaryTwoLayerTransfer_target_isConnectivity_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryTwoLayerTransfer_target_isConnectivity_of_pos_eq
  {W : Nat}
  {q : Real}
  {source target : FKRectBoundaryState W}
-- given
  (hW : 0 < W)
  (hq : 0 < q)
  (hpos : 0 < fkRectBoundaryTwoLayerTransfer hW q source target) :
-- imply
  target.IsConnectivity := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryTwoLayerTransfer_target_isConnectivity_of_pos hW hq source target hpos

/--
[fkRectBoundaryConnectivityLayerTransfer_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryConnectivityLayerTransfer_nonneg_eq
  {W : Nat}
  {q : Real}
  {evenRow : Bool}
  {source target : FKRectBoundaryConnectivityState W}
-- given
  (hW : 0 < W)
  (hq : 0 < q) :
-- imply
  0 <= fkRectBoundaryConnectivityLayerTransfer hW q evenRow source target := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryConnectivityLayerTransfer_nonneg hW hq evenRow source target

/--
[fkRectBoundaryConnectivityLayerTransfer_diag_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryConnectivityLayerTransfer_diag_pos_eq
  {W : Nat}
  {q : Real}
  {evenRow : Bool}
  {state : FKRectBoundaryConnectivityState W}
-- given
  (hW : 0 < W)
  (hq : 0 < q) :
-- imply
  0 < fkRectBoundaryConnectivityLayerTransfer hW q evenRow state state := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryConnectivityLayerTransfer_diag_pos hW hq evenRow state

/--
[fkRectBoundaryConnectivityTwoLayerTransfer_diag_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryConnectivityTwoLayerTransfer_diag_pos_eq
  {W : Nat}
  {q : Real}
  {state : FKRectBoundaryConnectivityState W}
-- given
  (hW : 0 < W)
  (hq : 0 < q) :
-- imply
  0 < fkRectBoundaryConnectivityTwoLayerTransfer hW q state state := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryConnectivityTwoLayerTransfer_diag_pos hW hq state

/--
[fkRectBoundaryLayerTransfer_diag_pos_of_isConnectivity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryLayerTransfer_diag_pos_of_isConnectivity_eq
  {W : Nat}
  {q : Real}
  {evenRow : Bool}
  {state : FKRectBoundaryState W}
-- given
  (hW : 0 < W)
  (hq : 0 < q)
  (hstate : state.IsConnectivity) :
-- imply
  0 < fkRectBoundaryLayerTransfer hW q evenRow state state := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryLayerTransfer_diag_pos_of_isConnectivity hW hq evenRow state hstate

/--
[fkRectBoundaryTwoLayerTransfer_diag_pos_of_isConnectivity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryTwoLayerTransfer_diag_pos_of_isConnectivity_eq
  {W : Nat}
  {q : Real}
  {state : FKRectBoundaryState W}
-- given
  (hW : 0 < W)
  (hq : 0 < q)
  (hstate : state.IsConnectivity) :
-- imply
  0 < fkRectBoundaryTwoLayerTransfer hW q state state := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryTwoLayerTransfer_diag_pos_of_isConnectivity hW hq state hstate

/--
[fkRectBoundaryTwoLayerTransfer_reachable_isConnectivity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryTwoLayerTransfer_reachable_isConnectivity_eq
  {W : Nat}
  {q : Real}
  {state : FKRectBoundaryState W}
-- given
  (hW : 0 < W)
  (hq : 0 < q)
  (hreach : MatrixPositiveReachable (fkRectBoundaryTwoLayerTransfer hW q) (fkRectBoundaryInitialState W) state) :
-- imply
  state.IsConnectivity := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryTwoLayerTransfer_reachable_isConnectivity hW hq state hreach

/--
[fkRectBoundaryLayerTransfer_mulVec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryLayerTransfer_mulVec_eq
  {W : Nat}
  {q : Real}
  {evenRow : Bool}
  {source : FKRectBoundaryState W}
-- given
  (hW : 0 < W)
  (f : FKRectBoundaryState W -> Real) :
-- imply
  (fkRectBoundaryLayerTransfer hW q evenRow *ᵥ f) source = ∑ eta : Bool × Fin W -> Bool, fkRectBoundaryLayerWeight hW q evenRow source eta * f (fkRectBoundaryLayerOutput hW evenRow source eta) := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryLayerTransfer_mulVec hW q evenRow f source

/--
[fkRectBoundaryTwoLayerTransfer_mulVec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryTwoLayerTransfer_mulVec_eq
  {W : Nat}
  {q : Real}
  {source : FKRectBoundaryState W}
-- given
  (hW : 0 < W)
  (f : FKRectBoundaryState W -> Real) :
-- imply
  (fkRectBoundaryTwoLayerTransfer hW q *ᵥ f) source = ∑ oddLayer : Bool × Fin W -> Bool, fkRectBoundaryLayerWeight hW q false source oddLayer * ∑ evenLayer : Bool × Fin W -> Bool, fkRectBoundaryLayerWeight hW q true (fkRectBoundaryLayerOutput hW false source oddLayer) evenLayer * f (fkRectBoundaryLayerOutput hW true (fkRectBoundaryLayerOutput hW false source oddLayer) evenLayer) := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryTwoLayerTransfer_mulVec hW q f source

/--
[fkRectBoundarySeamFunctional_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundarySeamFunctional_pos_eq
  {W : Nat}
  {q : Real}
  {state : FKRectBoundaryState W}
-- given
  (hW : 0 < W)
  (hq : 0 < q) :
-- imply
  0 < fkRectBoundarySeamFunctional hW q state := by
-- proof
  apply StatMech.FrontierD.fkRectBoundarySeamFunctional_pos hW hq state

/--
[fkRectBoundaryFinalFunctional_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryFinalFunctional_pos_eq
  {W : Nat}
  {q : Real}
  {state : FKRectBoundaryState W}
-- given
  (hW : 0 < W)
  (hq : 0 < q) :
-- imply
  0 < (fkRectBoundaryLayerTransfer hW q false *ᵥ fkRectBoundarySeamFunctional hW q) state := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryFinalFunctional_pos hW hq state

/--
[exists_fkRectBoundaryTransferReducedZ_log_div_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma exists_fkRectBoundaryTransferReducedZ_log_div_tendsto_eq
  {W : Nat}
  {q : Real}
-- given
  (hW : 0 < W)
  (hq : 0 < q) :
-- imply
  ∃ rate : Real, Tendsto (fun blocks : Nat => Real.log (fkRectBoundaryTransferReducedZ hW q blocks) / (blocks : Real)) atTop (nhds rate) := by
-- proof
  apply StatMech.FrontierD.exists_fkRectBoundaryTransferReducedZ_log_div_tendsto hW hq

/--
[fkRectBoundaryListCoefficientSum_alternating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryListCoefficientSum_alternating_eq
  {W : Nat}
  {q : Real}
  {state : FKRectBoundaryState W}
  {blocks : Nat}
-- given
  (hW : 0 < W) :
-- imply
  fkRectBoundaryListCoefficientSum hW q state (fkRectBoundaryAlternatingParityList blocks) = fkRectBoundaryAlternatingCoefficientSum hW q state blocks := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryListCoefficientSum_alternating hW q state blocks

/--
[fkRectBoundaryAlternatingCoefficientSum_eq_matrix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryAlternatingCoefficientSum_eq_matrix_eq
  {W : Nat}
  {q : Real}
  {state : FKRectBoundaryState W}
  {blocks : Nat}
-- given
  (hW : 0 < W) :
-- imply
  fkRectBoundaryAlternatingCoefficientSum hW q state blocks = ((((fkRectBoundaryTwoLayerTransfer hW q) ^ blocks * fkRectBoundaryLayerTransfer hW q false) *ᵥ fkRectBoundarySeamFunctional hW q) state) := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryAlternatingCoefficientSum_eq_matrix hW q state blocks

/--
[fkRectBoundaryTransferReducedZ_eq_coefficientSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryTransferReducedZ_eq_coefficientSum_eq
  {W : Nat}
  {q : Real}
  {blocks : Nat}
-- given
  (hW : 0 < W) :
-- imply
  fkRectBoundaryTransferReducedZ hW q blocks = fkRectBoundaryAlternatingCoefficientSum hW q (fkRectBoundaryInitialState W) blocks := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryTransferReducedZ_eq_coefficientSum hW q blocks

/--
[fkRectCriticalReducedZ_eq_boundaryTransferReducedZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectCriticalReducedZ_eq_boundaryTransferReducedZ_eq
  {R : FKRectTorus}
  {q : Real}
  {blocks : Nat}
-- given
  (hheight : R.height = 2 * (blocks + 1)) :
-- imply
  fkRectCriticalReducedZ R q = fkRectBoundaryTransferReducedZ R.width_pos q blocks := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalReducedZ_eq_boundaryTransferReducedZ R q blocks hheight

/--
[fkRectBoundaryTransferReducedZ_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean)
-/
@[path]
private lemma fkRectBoundaryTransferReducedZ_zero_eq
  {W : Nat}
  {q : Real}
-- given
  (hW : 0 < W) :
-- imply
  fkRectBoundaryTransferReducedZ hW q 0 = ∑ oddLayer : Bool × Fin W -> Bool, fkRectBoundaryLayerWeight hW q false (fkRectBoundaryInitialState W) oddLayer * fkRectBoundarySeamFunctional hW q (fkRectBoundaryLayerOutput hW false (fkRectBoundaryInitialState W) oddLayer) := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryTransferReducedZ_zero hW q


-- created on 2026-10-23
