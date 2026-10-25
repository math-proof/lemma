import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc71spanningtree.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc71_deg3_of_three_neighbours](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc71spanningtree.lean)
-/
@[path]
private lemma bc71_deg3_of_three_neighbours_eq
  {d : ℕ}
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {u a₁ a₂ a₃ : V}
-- given
  (h₁ : G.Adj u a₁)
  (h₂ : G.Adj u a₂)
  (h₃ : G.Adj u a₃)
  (h12 : a₁ ≠ a₂)
  (h13 : a₁ ≠ a₃)
  (h23 : a₂ ≠ a₃) :
-- imply
  3 ≤ G.degree u := by
-- proof
  apply StatMech.Walls.bc71_deg3_of_three_neighbours G h₁ h₂ h₃ h12 h13 h23

/--
[bc71_cutArms_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc71spanningtree.lean)
-/
@[path]
private lemma bc71_cutArms_distinct_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y a₁ a₂ a₃ : Site d}
-- given
  (hcut₁₂ : ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂)
  (hcut₁₃ : ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃)
  (hcut₂₃ : ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) :
-- imply
  a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃ := by
-- proof
  apply StatMech.Walls.bc71_cutArms_distinct ω L hcut₁₂ hcut₁₃ hcut₂₃

/--
[bc71_Gn_trifurcation_arms_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc71spanningtree.lean)
-/
@[path]
private lemma bc71_Gn_trifurcation_arms_distinct_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d}
-- given
  (h : bc67_IsGnTrifurcation ω L y) :
-- imply
  ∃ a₁ a₂ a₃ : Site d, (bc67_GnIncident ω L y a₁ ∧ bc67_GnIncident ω L y a₂ ∧ bc67_GnIncident ω L y a₃) ∧ (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) := by
-- proof
  apply StatMech.Walls.bc71_Gn_trifurcation_arms_distinct ω L h

/--
[bc71_deg3_of_cutArms_subtype](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc71spanningtree.lean)
-/
@[path]
private lemma bc71_deg3_of_cutArms_subtype_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d}
  {S : Set (Site d)}
  [Fintype (↑S : Type)]
  {G : SimpleGraph (↑S : Type)}
  [DecidableRel G.Adj]
  {u v₁ v₂ v₃ : (↑S : Type)}
-- given
  (hadj₁ : G.Adj u v₁)
  (hadj₂ : G.Adj u v₂)
  (hadj₃ : G.Adj u v₃)
  (hcut₁₂ : ¬ (bc67_contractedLattice ω L y).Reachable (v₁ : Site d) (v₂ : Site d))
  (hcut₁₃ : ¬ (bc67_contractedLattice ω L y).Reachable (v₁ : Site d) (v₃ : Site d))
  (hcut₂₃ : ¬ (bc67_contractedLattice ω L y).Reachable (v₂ : Site d) (v₃ : Site d)) :
-- imply
  3 ≤ G.degree u := by
-- proof
  apply StatMech.Walls.bc71_deg3_of_cutArms_subtype ω L y G hadj₁ hadj₂ hadj₃ hcut₁₂ hcut₁₃ hcut₂₃

/--
[bc71_globalForest_of_forestNeighbours](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc71spanningtree.lean)
-/
@[path]
private lemma bc71_globalForest_of_forestNeighbours_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc71_GnForestNeighbours ω L R) :
-- imply
  bc69_Gn_globalForest ω L R := by
-- proof
  apply StatMech.Walls.bc71_globalForest_of_forestNeighbours ω L R h

/--
[bc71_count_of_forestNeighbours](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc71spanningtree.lean)
-/
@[path]
private lemma bc71_count_of_forestNeighbours_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc71_GnForestNeighbours ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc71_count_of_forestNeighbours ω L R h

/--
[bc71_infiniteClusters_top_null_of_forestNeighbours](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc71spanningtree.lean)
-/
@[path]
private lemma bc71_infiniteClusters_top_null_of_forestNeighbours_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hNbr : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc71_GnForestNeighbours ω L R)
  (hcoarseRoute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} → ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d, 0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc71_infiniteClusters_top_null_of_forestNeighbours μ hd hinv hfe L hNbr hcoarseRoute

/--
[bc71_Gn_spanForest_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc71spanningtree.lean)
-/
@[path]
private lemma bc71_Gn_spanForest_degree_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {R : ℕ}
  {L : ℕ}
  {y : Site d}
  {v₁ v₂ v₃ : (↑(box d R) : Type)}
-- given
  (hy : y ∈ box d R)
  (hadj₁ : (bc70_spanningForest ω R).Adj ⟨y, hy⟩ v₁)
  (hadj₂ : (bc70_spanningForest ω R).Adj ⟨y, hy⟩ v₂)
  (hadj₃ : (bc70_spanningForest ω R).Adj ⟨y, hy⟩ v₃)
  (hcut₁₂ : ¬ (bc67_contractedLattice ω L y).Reachable (v₁ : Site d) (v₂ : Site d))
  (hcut₁₃ : ¬ (bc67_contractedLattice ω L y).Reachable (v₁ : Site d) (v₃ : Site d))
  (hcut₂₃ : ¬ (bc67_contractedLattice ω L y).Reachable (v₂ : Site d) (v₃ : Site d)) :
-- imply
  3 ≤ (bc70_spanningForest ω R).degree ⟨y, hy⟩ := by
-- proof
  apply StatMech.Walls.bc71_Gn_spanForest_degree ω R L hy hadj₁ hadj₂ hadj₃ hcut₁₂ hcut₁₃ hcut₂₃

/--
[bc71_upperLines_deg3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc71spanningtree.lean)
-/
@[path]
private lemma bc71_upperLines_deg3_eq
  {d : ℕ}
  {L R : ℕ}
-- given
  (hL : 3 ≤ L)
  (hR3 : 4 ≤ R)
  (hsingle : ∀ y, y ∈ box 2 R → bc67_IsGnTrifurcation bc60_upperLines L y → y = 0) :
-- imply
  bc69_Gn_globalForest bc60_upperLines L R := by
-- proof
  apply StatMech.Walls.bc71_upperLines_deg3 hL hR3 hsingle

/--
[bc71_star_centre_deg3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc71spanningtree.lean)
-/
@[path]
private lemma bc71_star_centre_deg3_eq
  {d : ℕ} :
-- imply
  bc70_star4.degree 0 = 3 := by
-- proof
  apply StatMech.Walls.bc71_star_centre_deg3

/--
[bc71_degree_collapse_possible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc71spanningtree.lean)
-/
@[path]
private lemma bc71_degree_collapse_possible_eq
  {d : ℕ} :
-- imply
  ∃ (D : ℕ) (ω : ConfigSpace (Sym2 (Site D))) (L : ℕ) (y a b : Site D), b ∈ bc61_boxAround D L y ∧ (openSubgraph D ω).Adj b a ∧ bc67_GnIncident ω L y a ∧ ¬ (hypercubicLattice D).Adj y a := by
-- proof
  apply StatMech.Walls.bc71_degree_collapse_possible

/--
[bc71_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc71spanningtree.lean)
-/
@[path]
private lemma bc71_status_eq
  {d : ℕ} :
-- imply
  (∀ {V : Type} [Fintype V] (G : SimpleGraph V) [_inst : DecidableRel G.Adj] (u a₁ a₂ a₃ : V), G.Adj u a₁ → G.Adj u a₂ → G.Adj u a₃ → a₁ ≠ a₂ → a₁ ≠ a₃ → a₂ ≠ a₃ → 3 ≤ G.degree u) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a₁ a₂ a₃ : Site d), ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ → ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ → ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃ → a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bc71_GnForestNeighbours ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
-- proof
  apply StatMech.Walls.bc71_status


-- created on 2026-10-23
