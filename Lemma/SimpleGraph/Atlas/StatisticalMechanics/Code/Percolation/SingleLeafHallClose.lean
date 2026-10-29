import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.SingleLeafHallClose.Part2
open Set SimpleGraph Finset MeasureTheory StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[slh_cut_neighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SingleLeafHallClose.lean)
-/
@[path]
private lemma slh_cut_neighbor_eq
  {d : ℕ}
  [DecidableEq W]
  {G : SimpleGraph W}
  {x a : W}
-- given
  (hxa : x ≠ a)
  (h : G.Reachable x a) :
-- imply
  ∃ (c : W) (hc : c ≠ x) (ha : a ≠ x), G.Adj x c ∧ (G.induce ({x}ᶜ : Set W)).Reachable ⟨c, by simpa using hc⟩ ⟨a, by simpa using ha⟩ := by
-- proof
  apply StatMech.Percolation.slh_cut_neighbor hxa h

/--
[slh_deg_ge_three_of_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SingleLeafHallClose.lean)
-/
@[path]
private lemma slh_deg_ge_three_of_cut_eq
  {d : ℕ}
  [DecidableEq W]
  [Fintype W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {x a₁ a₂ a₃ : W}
-- given
  (hr₁ : G.Reachable x a₁)
  (hr₂ : G.Reachable x a₂)
  (hr₃ : G.Reachable x a₃)
  (hx₁ : x ≠ a₁)
  (hx₂ : x ≠ a₂)
  (hx₃ : x ≠ a₃)
  (hcut₁₂ : ¬ (G.induce ({x}ᶜ : Set W)).Reachable ⟨a₁, by simpa using hx₁.symm⟩ ⟨a₂, by simpa using hx₂.symm⟩)
  (hcut₁₃ : ¬ (G.induce ({x}ᶜ : Set W)).Reachable ⟨a₁, by simpa using hx₁.symm⟩ ⟨a₃, by simpa using hx₃.symm⟩)
  (hcut₂₃ : ¬ (G.induce ({x}ᶜ : Set W)).Reachable ⟨a₂, by simpa using hx₂.symm⟩ ⟨a₃, by simpa using hx₃.symm⟩) :
-- imply
  3 ≤ G.degree x := by
-- proof
  apply StatMech.Percolation.slh_deg_ge_three_of_cut hr₁ hr₂ hr₃ hx₁ hx₂ hx₃ hcut₁₂ hcut₁₃ hcut₂₃

/--
[slh_edge_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SingleLeafHallClose.lean)
-/
@[path]
private lemma slh_edge_transfer_eq
  {d : ℕ}
  {x u v : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hadj : (openSubgraph d ω).Adj u v)
  (hux : u ≠ x)
  (hvx : v ≠ x) :
-- imply
  (openSubgraph d (removeSite x ω)).Adj u v := by
-- proof
  apply StatMech.Percolation.slh_edge_transfer x u v ω hadj hux hvx

/--
[slh_walk_avoid_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SingleLeafHallClose.lean)
-/
@[path]
private lemma slh_walk_avoid_transfer_eq
  {d : ℕ}
  {x u v : Site d}
  {ω : ConfigSpace (Sym2 (Site d))}
  {w : (openSubgraph d ω).Walk u v}
-- given
  (hw : x ∉ w.support) :
-- imply
  (openSubgraph d (removeSite x ω)).Reachable u v := by
-- proof
  apply StatMech.Percolation.slh_walk_avoid_transfer w hw

/--
[slh_connected_removeSite_of_G_induce](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SingleLeafHallClose.lean)
-/
@[path]
private lemma slh_connected_removeSite_of_G_induce_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : SimpleGraph W}
  {π : W → Site d}
  {p wi wj : W}
-- given
  (hπ : ∀ u v, G.Adj u v → (openSubgraph d ω).Adj (π u) (π v))
  (hπinj : Function.Injective π)
  (hwi : wi ≠ p)
  (hwj : wj ≠ p)
  (h : (G.induce ({p}ᶜ : Set W)).Reachable ⟨wi, by simpa using hwi⟩ ⟨wj, by simpa using hwj⟩) :
-- imply
  Connected d (removeSite (π p) ω) (π wi) (π wj) := by
-- proof
  apply StatMech.Percolation.slh_connected_removeSite_of_G_induce π hπ hπinj hwi hwj h

/--
[slh_spanningTreeLeafCount_of_treeForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SingleLeafHallClose.lean)
-/
@[path]
private lemma slh_spanningTreeLeafCount_of_treeForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : slh_TreeForestData ω n) :
-- imply
  flc2_SpanningTreeLeafCount ω n := by
-- proof
  apply StatMech.Percolation.slh_spanningTreeLeafCount_of_treeForest ω n h

/--
[slh_Tcount_le_boundary_of_treeForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SingleLeafHallClose.lean)
-/
@[path]
private lemma slh_Tcount_le_boundary_of_treeForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : slh_TreeForestData ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.slh_Tcount_le_boundary_of_treeForest ω n h

/--
[slh_treeForestData_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SingleLeafHallClose.lean)
-/
@[path]
private lemma slh_treeForestData_of_noTrif_eq
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
  slh_TreeForestData ω n := by
-- proof
  apply StatMech.Percolation.slh_treeForestData_of_noTrif ω n hz₀ hz₁ hopen hno

/--
[slh_claw_survives_branchingCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SingleLeafHallClose.lean)
-/
@[path]
private lemma slh_claw_survives_branchingCount_eq
  {d : ℕ}
  [Fintype W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
-- given
  (hTree : G.IsTree)
  (hWcard : 2 ≤ Fintype.card W) :
-- imply
  (univ.filter (fun v => 3 ≤ G.degree v)).card < (univ.filter (fun v => G.degree v = 1)).card := by
-- proof
  apply StatMech.Percolation.slh_claw_survives_branchingCount G hTree hWcard

/--
[slh_burton_keane_bernoulli_of_treeForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SingleLeafHallClose.lean)
-/
@[path]
private lemma slh_burton_keane_bernoulli_of_treeForest_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → slh_TreeForestData ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.slh_burton_keane_bernoulli_of_treeForest hd p hp1 hp0 hres htrif


-- created on 2026-10-23
