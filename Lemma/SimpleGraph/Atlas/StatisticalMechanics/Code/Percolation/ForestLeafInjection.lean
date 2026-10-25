import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.ForestLeafInjection
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[fli_satSet_closed_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafInjection.lean)
-/
@[path]
private lemma fli_satSet_closed_adj_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {S : Finset V}
  {v w : V}
-- given
  (hadj : G.Adj v w)
  (hv : v ∈ fli_satSet G S) :
-- imply
  w ∈ fli_satSet G S := by
-- proof
  apply StatMech.Percolation.fli_satSet_closed_adj G hadj hv

/--
[fli_satSet_neighborSet_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafInjection.lean)
-/
@[path]
private lemma fli_satSet_neighborSet_subset_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {S : Finset V}
  {v : V}
-- given
  (hv : v ∈ fli_satSet G S) :
-- imply
  G.neighborSet v ⊆ fli_satSet G S := by
-- proof
  apply StatMech.Percolation.fli_satSet_neighborSet_subset G hv

/--
[fli_mem_satSet_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafInjection.lean)
-/
@[path]
private lemma fli_mem_satSet_of_mem_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {S : Finset V}
  {x : V}
-- given
  (hx : x ∈ S) :
-- imply
  x ∈ fli_satSet G S := by
-- proof
  apply StatMech.Percolation.fli_mem_satSet_of_mem G hx

/--
[fli_forest_leaf_hall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafInjection.lean)
-/
@[path]
private lemma fli_forest_leaf_hall_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
-- given
  (hacyc : G.IsAcyclic)
  (hmin : ∀ v, 1 ≤ G.degree v)
  (hS3 : ∀ x ∈ S, 3 ≤ G.degree x) :
-- imply
  S.card ≤ (S.biUnion (fun x => univ.filter (fun ℓ => G.degree ℓ = 1 ∧ G.Reachable x ℓ))).card := by
-- proof
  apply StatMech.Percolation.fli_forest_leaf_hall G hacyc hmin S hS3

/--
[fli_branch_leaf_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafInjection.lean)
-/
@[path]
private lemma fli_branch_leaf_injection_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
-- given
  (hacyc : G.IsAcyclic)
  (hmin : ∀ v, 1 ≤ G.degree v)
  (hS3 : ∀ x ∈ S, 3 ≤ G.degree x) :
-- imply
  ∃ ψ : V → V, (∀ x ∈ S, G.degree (ψ x) = 1 ∧ G.Reachable x (ψ x)) ∧ Set.InjOn ψ S := by
-- proof
  apply StatMech.Percolation.fli_branch_leaf_injection G hacyc hmin S hS3

/--
[fli_reachable_to_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafInjection.lean)
-/
@[path]
private lemma fli_reachable_to_connected_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {Vset : Finset (Site d)}
  {F : SimpleGraph (↑Vset : Type)}
  [DecidableRel F.Adj]
  {u v : (↑Vset : Type)}
-- given
  (hπ : ∀ u v, F.Adj u v → (openSubgraph d ω).Adj (u : Site d) (v : Site d))
  (h : F.Reachable u v) :
-- imply
  Connected d ω (u : Site d) (v : Site d) := by
-- proof
  apply StatMech.Percolation.fli_reachable_to_connected hπ h

/--
[fli_distinctArmEnds_of_boxOpenForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafInjection.lean)
-/
@[path]
private lemma fli_distinctArmEnds_of_boxOpenForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bst_BoxOpenForest ω n) :
-- imply
  tfc_DistinctArmEnds ω n := by
-- proof
  apply StatMech.Percolation.fli_distinctArmEnds_of_boxOpenForest ω n h

/--
[fli_Tcount_le_boundary_of_boxOpenForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafInjection.lean)
-/
@[path]
private lemma fli_Tcount_le_boundary_of_boxOpenForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bst_BoxOpenForest ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.fli_Tcount_le_boundary_of_boxOpenForest ω n h

/--
[fli_burton_keane_bernoulli_of_boxOpenForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafInjection.lean)
-/
@[path]
private lemma fli_burton_keane_bernoulli_of_boxOpenForest_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bst_BoxOpenForest ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.fli_burton_keane_bernoulli_of_boxOpenForest hd p hp1 hp0 hres htrif

/--
[fli_star_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafInjection.lean)
-/
@[path]
private lemma fli_star_injection_eq
  {d : ℕ} :
-- imply
  ∃ ψ : Fin 4 → Fin 4, (∀ x ∈ ({0} : Finset (Fin 4)), Flc2Witness.starG.degree (ψ x) = 1 ∧ Flc2Witness.starG.Reachable x (ψ x)) ∧ Set.InjOn ψ ({0} : Finset (Fin 4)) := by
-- proof
  apply StatMech.Percolation.fli_star_injection

/--
[fli_star_hall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafInjection.lean)
-/
@[path]
private lemma fli_star_hall_eq
  {d : ℕ} :
-- imply
  ({0} : Finset (Fin 4)).card ≤ (({0} : Finset (Fin 4)).biUnion (fun x => univ.filter (fun ℓ => Flc2Witness.starG.degree ℓ = 1 ∧ Flc2Witness.starG.Reachable x ℓ))).card := by
-- proof
  apply StatMech.Percolation.fli_star_hall

/--
[fli_path_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafInjection.lean)
-/
@[path]
private lemma fli_path_injection_eq
  {d : ℕ} :
-- imply
  ∃ ψ : Fin 2 → Fin 2, (∀ x ∈ (∅ : Finset (Fin 2)), Flc2Witness.pathG.degree (ψ x) = 1 ∧ Flc2Witness.pathG.Reachable x (ψ x)) ∧ Set.InjOn ψ (∅ : Finset (Fin 2)) := by
-- proof
  apply StatMech.Percolation.fli_path_injection


-- created on 2026-10-23
