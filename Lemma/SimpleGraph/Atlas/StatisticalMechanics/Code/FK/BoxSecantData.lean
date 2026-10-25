import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.BoxSecantData
open Filter Topology SimpleGraph StatMech StatMech.FK


/--
[boxSecantVolume_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxSecantData.lean)
-/
@[path]
private lemma boxSecantVolume_pos_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  0 < boxSecantVolume d n := by
-- proof
  apply StatMech.FK.boxSecantVolume_pos hd n

/--
[boxSecantSurface_div_volume_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxSecantData.lean)
-/
@[path]
private lemma boxSecantSurface_div_volume_eq_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  boxSecantSurface d n / boxSecantVolume d n = 2 / (2 * n + 1) := by
-- proof
  apply StatMech.FK.boxSecantSurface_div_volume_eq hd n

/--
[boxSecant_two_div_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxSecantData.lean)
-/
@[path]
private lemma boxSecant_two_div_tendsto_zero_eq :
-- imply
  Tendsto (fun n : ℕ => (2 : ℝ) / (2 * n + 1)) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.boxSecant_two_div_tendsto_zero

/--
[boxSecantSurface_div_volume_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxSecantData.lean)
-/
@[path]
private lemma boxSecantSurface_div_volume_tendsto_zero_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  Tendsto (fun n => boxSecantSurface d n / boxSecantVolume d n) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.boxSecantSurface_div_volume_tendsto_zero hd

/--
[boxSecantVolume_tendsto_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxSecantData.lean)
-/
@[path]
private lemma boxSecantVolume_tendsto_atTop_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  Tendsto (fun n => boxSecantVolume d n) atTop atTop := by
-- proof
  apply StatMech.FK.boxSecantVolume_tendsto_atTop hd

/--
[boxSecant_surface_volume_asymptotics](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxSecantData.lean)
-/
@[path]
private lemma boxSecant_surface_volume_asymptotics_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d) :
-- imply
  (∀ n, 0 < boxSecantVolume d n) ∧ Tendsto (fun n => boxSecantSurface d n / boxSecantVolume d n) atTop (𝓝 0) ∧ Tendsto (fun n => boxSecantVolume d n) atTop atTop := by
-- proof
  apply StatMech.FK.boxSecant_surface_volume_asymptotics hd

/--
[connectedComponent_card_le_add_of_sup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxSecantData.lean)
-/
@[path]
private lemma connectedComponent_card_le_add_of_sup_eq
  [Fintype V]
  {G K : SimpleGraph V}
  {p : V → Prop}
-- given
  (hK : ∀ {x y}, K.Adj x y → p x ∧ p y) :
-- imply
  Nat.card G.ConnectedComponent ≤ Nat.card (G ⊔ K).ConnectedComponent + Nat.card {v // p v} := by
-- proof
  apply StatMech.FK.connectedComponent_card_le_add_of_sup hK

/--
[natCard_boundary_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxSecantData.lean)
-/
@[path]
private lemma natCard_boundary_eq_eq
  [Fintype V]
  [DecidableEq V]
  [DecidablePred bdry]
-- given
  (bdry : V → Prop) :
-- imply
  Nat.card {v // bdry v} = (Finset.univ.filter bdry).card := by
-- proof
  apply StatMech.FK.natCard_boundary_eq bdry

/--
[numClustersFree_le_numClustersWired_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxSecantData.lean)
-/
@[path]
private lemma numClustersFree_le_numClustersWired_add_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {ω : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop) :
-- imply
  numClustersFree G ω ≤ numClustersWired G bdry ω + (Finset.univ.filter bdry).card := by
-- proof
  apply StatMech.FK.numClustersFree_le_numClustersWired_add G bdry ω

/--
[numClusters_wired_sandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxSecantData.lean)
-/
@[path]
private lemma numClusters_wired_sandwich_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidablePred bdry]
  {ω : ConfigSpace (Sym2 V)}
-- given
  (bdry : V → Prop) :
-- imply
  numClustersWired G bdry ω ≤ numClustersFree G ω ∧ numClustersFree G ω ≤ numClustersWired G bdry ω + (Finset.univ.filter bdry).card := by
-- proof
  apply StatMech.FK.numClusters_wired_sandwich G bdry ω

/--
[box_numClusters_wired_sandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxSecantData.lean)
-/
@[path]
private lemma box_numClusters_wired_sandwich_eq
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))} :
-- imply
  numClustersWired (boxGraph d n) (boxBoundary d n) ω ≤ numClustersFree (boxGraph d n) ω ∧ numClustersFree (boxGraph d n) ω ≤ numClustersWired (boxGraph d n) (boxBoundary d n) ω + (Finset.univ.filter (boxBoundary d n)).card := by
-- proof
  apply StatMech.FK.box_numClusters_wired_sandwich d n ω


-- created on 2026-10-23
