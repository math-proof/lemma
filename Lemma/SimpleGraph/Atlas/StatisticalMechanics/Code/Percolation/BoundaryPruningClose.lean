import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.BoundaryPruningClose.Part2
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[bpr_treeForestData_slh_refutable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BoundaryPruningClose.lean)
-/
@[path]
private lemma bpr_treeForestData_slh_refutable_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Site d}
-- given
  (hxbox : x ∈ box d n)
  (htri : IsTrifurcation d ω x) :
-- imply
  ¬ slh_TreeForestData ω n := by
-- proof
  apply StatMech.Percolation.bpr_treeForestData_slh_refutable ω n x hxbox htri

/--
[bpr_spanningTreeLeafCount_of_treeForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BoundaryPruningClose.lean)
-/
@[path]
private lemma bpr_spanningTreeLeafCount_of_treeForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bpr_TreeForestData ω n) :
-- imply
  flc2_SpanningTreeLeafCount ω n := by
-- proof
  apply StatMech.Percolation.bpr_spanningTreeLeafCount_of_treeForest ω n h

/--
[bpr_Tcount_le_boundary_of_treeForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BoundaryPruningClose.lean)
-/
@[path]
private lemma bpr_Tcount_le_boundary_of_treeForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bpr_TreeForestData ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.bpr_Tcount_le_boundary_of_treeForest ω n h

/--
[bpr_treeForestData_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BoundaryPruningClose.lean)
-/
@[path]
private lemma bpr_treeForestData_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {z₀ z₁ : Site d}
-- given
  (hz₀ : z₀ ∈ vertexBoundary d n)
  (hz₁ : z₁ ∈ vertexBoundary d n)
  (hopen : (openSubgraph d ω).Adj z₀ z₁)
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  bpr_TreeForestData ω n := by
-- proof
  apply StatMech.Percolation.bpr_treeForestData_of_noTrif ω n hz₀ hz₁ hopen hno

/--
[bpr_treeForestData_star](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BoundaryPruningClose.lean)
-/
@[path]
private lemma bpr_treeForestData_star_eq
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
  bpr_TreeForestData ω n := by
-- proof
  apply StatMech.Percolation.bpr_treeForestData_star ω n a hsingle hadj habdry hxne hainj hsep

/--
[bpr_burton_keane_bernoulli_of_treeForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BoundaryPruningClose.lean)
-/
@[path]
private lemma bpr_burton_keane_bernoulli_of_treeForest_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → bpr_TreeForestData ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.bpr_burton_keane_bernoulli_of_treeForest hd p hp1 hp0 hres htrif


-- created on 2026-10-23
