import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc70globalforest.Part4
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc70_Gn_clusterGraph_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc70globalforest.lean)
-/
@[path]
private lemma bc70_Gn_clusterGraph_adj_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {R : ℕ}
  {a b : (↑(box d R) : Type)} :
-- imply
  (bc70_Gn_clusterGraph ω R).Adj a b ↔ (openSubgraph d ω).Adj (a : Site d) (b : Site d) := by
-- proof
  apply StatMech.Walls.bc70_Gn_clusterGraph_adj ω R a b

/--
[bc70_spanningForest_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc70globalforest.lean)
-/
@[path]
private lemma bc70_spanningForest_acyclic_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {R : ℕ} :
-- imply
  (bc70_spanningForest ω R).IsAcyclic := by
-- proof
  apply StatMech.Walls.bc70_spanningForest_acyclic ω R

/--
[bc70_spanningForest_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc70globalforest.lean)
-/
@[path]
private lemma bc70_spanningForest_le_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {R : ℕ} :
-- imply
  bc70_spanningForest ω R ≤ bc70_Gn_clusterGraph ω R := by
-- proof
  apply StatMech.Walls.bc70_spanningForest_le ω R

/--
[bc70_spanningForest_reachable_of](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc70globalforest.lean)
-/
@[path]
private lemma bc70_spanningForest_reachable_of_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {R : ℕ}
  {a b : (↑(box d R) : Type)}
-- given
  (h : (bc70_Gn_clusterGraph ω R).Reachable a b) :
-- imply
  (bc70_spanningForest ω R).Reachable a b := by
-- proof
  apply StatMech.Walls.bc70_spanningForest_reachable_of ω R h

/--
[bc70_spanningForest_degree_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc70globalforest.lean)
-/
@[path]
private lemma bc70_spanningForest_degree_pos_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {R : ℕ}
  {u v : (↑(box d R) : Type)}
-- given
  (hv : v ≠ u)
  (h : (bc70_Gn_clusterGraph ω R).Reachable u v) :
-- imply
  1 ≤ (bc70_spanningForest ω R).degree u := by
-- proof
  apply StatMech.Walls.bc70_spanningForest_degree_pos ω R hv h

/--
[bc70_spanningForest_leaf_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc70globalforest.lean)
-/
@[path]
private lemma bc70_spanningForest_leaf_count_eq
  {d : ℕ}
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (hacyc : G.IsAcyclic)
  (hmin : ∀ v, 1 ≤ G.degree v) :
-- imply
  (univ.filter (fun v => 3 ≤ G.degree v)).card ≤ (univ.filter (fun v => G.degree v = 1)).card := by
-- proof
  apply StatMech.Walls.bc70_spanningForest_leaf_count G hacyc hmin

/--
[bc70_globalForest_of_structure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc70globalforest.lean)
-/
@[path]
private lemma bc70_globalForest_of_structure_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc70_GnForestStructure ω L R) :
-- imply
  bc69_Gn_globalForest ω L R := by
-- proof
  apply StatMech.Walls.bc70_globalForest_of_structure ω L R h

/--
[bc70_count_of_globalForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc70globalforest.lean)
-/
@[path]
private lemma bc70_count_of_globalForest_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : bc69_Gn_globalForest ω L R) :
-- imply
  bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc70_count_of_globalForest ω L R h

/--
[bc70_infiniteClusters_top_null_of_globalForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc70globalforest.lean)
-/
@[path]
private lemma bc70_infiniteClusters_top_null_of_globalForest_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hStructure : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc70_GnForestStructure ω L R)
  (hcoarseRoute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} → ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d, 0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc70_infiniteClusters_top_null_of_globalForest μ hd hinv hfe L hStructure hcoarseRoute

/--
[bc70_globalForest_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc70globalforest.lean)
-/
@[path]
private lemma bc70_globalForest_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {z₀ z₁ : Site d}
-- given
  (hz₀ : z₀ ∈ vertexBoundary d R)
  (hz₁ : z₁ ∈ vertexBoundary d R)
  (hzne : z₀ ≠ z₁)
  (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
-- imply
  bc69_Gn_globalForest ω L R := by
-- proof
  apply StatMech.Walls.bc70_globalForest_of_noTrif ω L R hz₀ hz₁ hzne hno

/--
[bc70_star4_deg0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc70globalforest.lean)
-/
@[path]
private lemma bc70_star4_deg0_eq
  {d : ℕ} :
-- imply
  bc70_star4.degree 0 = 3 := by
-- proof
  apply StatMech.Walls.bc70_star4_deg0

/--
[bc70_star4_deg_leaf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc70globalforest.lean)
-/
@[path]
private lemma bc70_star4_deg_leaf_eq
  {d : ℕ} :
-- imply
  ∀ i : Fin 4, i ≠ 0 → bc70_star4.degree i = 1 := by
-- proof
  apply StatMech.Walls.bc70_star4_deg_leaf

/--
[bc70_star4_deg_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc70globalforest.lean)
-/
@[path]
private lemma bc70_star4_deg_pos_eq
  {d : ℕ} :
-- imply
  ∀ i : Fin 4, 1 ≤ bc70_star4.degree i := by
-- proof
  apply StatMech.Walls.bc70_star4_deg_pos

/--
[bc70_star4_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc70globalforest.lean)
-/
@[path]
private lemma bc70_star4_acyclic_eq
  {d : ℕ} :
-- imply
  bc70_star4.IsAcyclic := by
-- proof
  apply StatMech.Walls.bc70_star4_acyclic

/--
[bc70_globalForest_of_singleStar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc70globalforest.lean)
-/
@[path]
private lemma bc70_globalForest_of_singleStar_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {x : Site d}
  {a : Fin 3 → Site d}
-- given
  (hxbox : x ∈ box d R)
  (hxtri : bc67_IsGnTrifurcation ω L x)
  (hsingle : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → y = x)
  (habdry : ∀ i, a i ∈ vertexBoundary d R)
  (hxne : ∀ i, a i ≠ x)
  (hainj : Function.Injective a) :
-- imply
  bc69_Gn_globalForest ω L R := by
-- proof
  apply StatMech.Walls.bc70_globalForest_of_singleStar ω L R a hxbox hxtri hsingle habdry hxne hainj

/--
[bc70_upperLines_arm_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc70globalforest.lean)
-/
@[path]
private lemma bc70_upperLines_arm_ne_zero_eq
  {d : ℕ}
  {R : ℕ}
  {i : Fin 3}
-- given
  (hR : 1 ≤ R) :
-- imply
  bc57_pt (R : ℤ) ((i : ℤ) + 1) ≠ (0 : Site 2) := by
-- proof
  apply StatMech.Walls.bc70_upperLines_arm_ne_zero hR i

/--
[bc70_upperLines_globalForest](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc70globalforest.lean)
-/
@[path]
private lemma bc70_upperLines_globalForest_eq
  {d : ℕ}
  {L R : ℕ}
-- given
  (hL : 3 ≤ L)
  (hR3 : 4 ≤ R)
  (hsingle : ∀ y, y ∈ box 2 R → bc67_IsGnTrifurcation bc60_upperLines L y → y = 0) :
-- imply
  bc69_Gn_globalForest bc60_upperLines L R := by
-- proof
  apply StatMech.Walls.bc70_upperLines_globalForest hL hR3 hsingle

/--
[bc70_upperLines_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc70globalforest.lean)
-/
@[path]
private lemma bc70_upperLines_count_eq
  {d : ℕ}
  {L R : ℕ}
-- given
  (hL : 3 ≤ L)
  (hR3 : 4 ≤ R)
  (hsingle : ∀ y, y ∈ box 2 R → bc67_IsGnTrifurcation bc60_upperLines L y → y = 0) :
-- imply
  bc61_coarseTcount bc60_upperLines L R ≤ boxSV_boundaryCard 2 R := by
-- proof
  apply StatMech.Walls.bc70_upperLines_count hL hR3 hsingle

/--
[bc70_globalForest_of_doubleStar](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc70globalforest.lean)
-/
@[path]
private lemma bc70_globalForest_of_doubleStar_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {x x' : Site d}
  {a a' : Fin 3 → Site d}
  {lab : Fin 8 → Site d}
-- given
  (hxtri : bc67_IsGnTrifurcation ω L x)
  (hx'tri : bc67_IsGnTrifurcation ω L x')
  (hpair : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → y = x ∨ y = x')
  (habdry : ∀ i, a i ∈ vertexBoundary d R)
  (habdry' : ∀ i, a' i ∈ vertexBoundary d R)
  (hlab : lab 0 = x ∧ lab 1 = a 0 ∧ lab 2 = a 1 ∧ lab 3 = a 2 ∧ lab 4 = x' ∧ lab 5 = a' 0 ∧ lab 6 = a' 1 ∧ lab 7 = a' 2)
  (hlabinj : Function.Injective lab) :
-- imply
  bc69_Gn_globalForest ω L R := by
-- proof
  apply StatMech.Walls.bc70_globalForest_of_doubleStar ω L R a a' hxtri hx'tri hpair habdry habdry' lab hlab hlabinj

/--
[bc70_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc70globalforest.lean)
-/
@[path]
private lemma bc70_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), (bc70_spanningForest ω R).IsAcyclic) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (x : Site d) (a : Fin 3 → Site d), x ∈ box d R → bc67_IsGnTrifurcation ω L x → (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → y = x) → (∀ i, a i ∈ vertexBoundary d R) → (∀ i, a i ≠ x) → Function.Injective a → bc69_Gn_globalForest ω L R) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), bc70_GnForestStructure ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
-- proof
  apply StatMech.Walls.bc70_status


-- created on 2026-10-23
