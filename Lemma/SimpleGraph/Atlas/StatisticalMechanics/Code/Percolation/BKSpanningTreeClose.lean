import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.BKSpanningTreeClose.Part2
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[bst_connected_has_spanningTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKSpanningTreeClose.lean)
-/
@[path]
private lemma bst_connected_has_spanningTree_eq
  {d : ℕ}
  {G : SimpleGraph V}
-- given
  (hG : G.Connected) :
-- imply
  ∃ T : SimpleGraph V, T ≤ G ∧ T.IsTree := by
-- proof
  apply StatMech.Percolation.bst_connected_has_spanningTree G hG

/--
[bst_treeForestData_one_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKSpanningTreeClose.lean)
-/
@[path]
private lemma bst_treeForestData_one_cluster_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x y : Site d}
-- given
  (h : bpr_TreeForestData ω n)
  (hxbox : x ∈ box d n)
  (hxtri : IsTrifurcation d ω x)
  (hybox : y ∈ box d n)
  (hytri : IsTrifurcation d ω y) :
-- imply
  Connected d ω x y := by
-- proof
  apply StatMech.Percolation.bst_treeForestData_one_cluster ω n h hxbox hxtri hybox hytri

/--
[bst_treeForestData_refutable_of_twoClusters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKSpanningTreeClose.lean)
-/
@[path]
private lemma bst_treeForestData_refutable_of_twoClusters_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x y : Site d}
-- given
  (hxbox : x ∈ box d n)
  (hxtri : IsTrifurcation d ω x)
  (hybox : y ∈ box d n)
  (hytri : IsTrifurcation d ω y)
  (hsep : ¬ Connected d ω x y) :
-- imply
  ¬ bpr_TreeForestData ω n := by
-- proof
  apply StatMech.Percolation.bst_treeForestData_refutable_of_twoClusters ω n hxbox hxtri hybox hytri hsep

/--
[bst_deg_ge_three_of_boxOpenForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKSpanningTreeClose.lean)
-/
@[path]
private lemma bst_deg_ge_three_of_boxOpenForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {Vset : Finset (Site d)}
  {F : SimpleGraph (↑Vset : Type)}
  [DecidableRel F.Adj]
  {vx : Site d → (↑Vset : Type)}
  {b : Site d → Fin 3 → (↑Vset : Type)}
  {x : Site d}
-- given
  (hπ : ∀ u v, F.Adj u v → (openSubgraph d ω).Adj (u : Site d) (v : Site d))
  (_hxbox : x ∈ box d n)
  (_htri : IsTrifurcation d ω x)
  (hvx : (vx x : Site d) = x)
  (hreach : ∀ i, F.Reachable (vx x) (b x i) ∧ b x i ≠ vx x)
  (hcut : ¬ Connected d (removeSite x ω) (b x 0 : Site d) (b x 1 : Site d) ∧ ¬ Connected d (removeSite x ω) (b x 0 : Site d) (b x 2 : Site d) ∧ ¬ Connected d (removeSite x ω) (b x 1 : Site d) (b x 2 : Site d)) :
-- imply
  3 ≤ F.degree (vx x) := by
-- proof
  apply StatMech.Percolation.bst_deg_ge_three_of_boxOpenForest hπ _hxbox _htri hvx hreach hcut

/--
[bst_Tcount_le_boundary_of_boxOpenForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKSpanningTreeClose.lean)
-/
@[path]
private lemma bst_Tcount_le_boundary_of_boxOpenForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bst_BoxOpenForest ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.bst_Tcount_le_boundary_of_boxOpenForest ω n h

/--
[bst_boxOpenForest_star](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKSpanningTreeClose.lean)
-/
@[path]
private lemma bst_boxOpenForest_star_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Site d}
  {a : Fin 3 → Site d}
-- given
  (hsingle : ∀ y, y ∈ box d n → IsTrifurcation d ω y → y = x)
  (hadj : ∀ i, (openSubgraph d ω).Adj x (a i))
  (habdry : ∀ i, a i ∈ vertexBoundary d n)
  (hxne : ∀ i, a i ≠ x)
  (hainj : Function.Injective a)
  (hsep : ¬ Connected d (removeSite x ω) (a 0) (a 1) ∧ ¬ Connected d (removeSite x ω) (a 0) (a 2) ∧ ¬ Connected d (removeSite x ω) (a 1) (a 2)) :
-- imply
  bst_BoxOpenForest ω n := by
-- proof
  apply StatMech.Percolation.bst_boxOpenForest_star ω n a hsingle hadj habdry hxne hainj hsep


-- created on 2026-10-23
