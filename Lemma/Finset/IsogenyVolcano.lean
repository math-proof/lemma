import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.IsogenyVolcano
open BigOperators
open Multigraph
open IsogenyVolcano


/--
[adj_comm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/IsogenyVolcano.lean)
-/
@[path]
private lemma adj_comm_eq
  {G : Multigraph V}
  {v w : V} :
-- imply
  G.Adj v w ↔ G.Adj w v := by
-- proof
  apply Multigraph.adj_comm G v w

/--
[connected_refl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/IsogenyVolcano.lean)
-/
@[path]
private lemma connected_refl_eq
  {G : Multigraph V}
  {v : V} :
-- imply
  G.Connected v v := by
-- proof
  apply Multigraph.connected_refl G v

/--
[degreeOn_compl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/IsogenyVolcano.lean)
-/
@[path]
private lemma degreeOn_compl_eq
  [Fintype V] [DecidablePred P]
  {G : Multigraph V}
  {v : V}
-- given
  (P : V → Prop) :
-- imply
  G.degree v = G.degreeOn v P + G.degreeOn v (fun w => ¬ P w) := by
-- proof
  apply Multigraph.degreeOn_compl G v P

/--
[degreeOn_congr](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/IsogenyVolcano.lean)
-/
@[path]
private lemma degreeOn_congr_eq
  [Fintype V]
  {G : Multigraph V}
  {v : V}
  {P Q : V → Prop} [DecidablePred P] [DecidablePred Q]
-- given
  (h : ∀ w, G.edgeMult v w > 0 → (P w ↔ Q w)) :
-- imply
  G.degreeOn v P = G.degreeOn v Q := by
-- proof
  apply Multigraph.degreeOn_congr G v h

/--
[descending_iff_ascending_symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/IsogenyVolcano.lean)
-/
@[path]
private lemma descending_iff_ascending_symm_eq
  {ℓ : ℕ}
  {C : IsogenyVolcano ℓ}
  {v w : C.V} :
-- imply
  C.IsDescendingEdge v w ↔ C.IsAscendingEdge w v := by
-- proof
  apply IsogenyVolcano.descending_iff_ascending_symm v w

/--
[ascending_iff_descending_symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/IsogenyVolcano.lean)
-/
@[path]
private lemma ascending_iff_descending_symm_eq
  {ℓ : ℕ}
  {C : IsogenyVolcano ℓ}
  {v w : C.V} :
-- imply
  C.IsAscendingEdge v w ↔ C.IsDescendingEdge w v := by
-- proof
  apply IsogenyVolcano.ascending_iff_descending_symm v w

/--
[edge_direction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/IsogenyVolcano.lean)
-/
@[path]
private lemma edge_direction_eq
  {ℓ : ℕ}
  {C : IsogenyVolcano ℓ}
  {v w : C.V}
-- given
  (h : C.graph.edgeMult v w > 0) :
-- imply
  C.IsHorizontalEdge v w ∨ C.IsDescendingEdge v w ∨
    C.IsAscendingEdge v w := by
-- proof
  apply IsogenyVolcano.edge_direction v w h

/--
[isSurface_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/IsogenyVolcano.lean)
-/
@[path]
private lemma isSurface_iff_eq
  {ℓ : ℕ}
  {C : IsogenyVolcano ℓ}
  {v : C.V} :
-- imply
  C.isSurface v ↔ (C.level v : ℕ) = 0 := by
-- proof
  apply IsogenyVolcano.isSurface_iff v

/--
[isFloor_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/IsogenyVolcano.lean)
-/
@[path]
private lemma isFloor_iff_eq
  {ℓ : ℕ}
  {C : IsogenyVolcano ℓ}
  {v : C.V} :
-- imply
  C.isFloor v ↔ (C.level v : ℕ) = C.depth := by
-- proof
  apply IsogenyVolcano.isFloor_iff v

/--
[surface_degreeOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/IsogenyVolcano.lean)
-/
@[path]
private lemma surface_degreeOn_eq
  {ℓ : ℕ}
  {C : IsogenyVolcano ℓ}
  {v : C.V}
-- given
  (hv : C.isSurface v) :
-- imply
  C.graph.degreeOn v (fun w => C.isSurface w) = C.surfaceDegree := by
-- proof
  apply IsogenyVolcano.surface_degreeOn v hv


-- created on 2026-10-20
