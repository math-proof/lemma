import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.CorridorConfinement.Part2
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[bcc_cluster_adjClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CorridorConfinement.lean)
-/
@[path]
private lemma bcc_cluster_adjClosed_eq
  {d : ℕ}
  {ϱ : ConfigSpace (Sym2 (Site d))}
  {a : Site d} :
-- imply
  ∀ u v, u ∈ cluster d ϱ a → (openSubgraph d ϱ).Adj u v → v ∈ cluster d ϱ a := by
-- proof
  apply StatMech.Percolation.bcc_cluster_adjClosed ϱ a

/--
[bcc_cluster_disjoint_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CorridorConfinement.lean)
-/
@[path]
private lemma bcc_cluster_disjoint_of_ne_eq
  {d : ℕ}
  {ϱ : ConfigSpace (Sym2 (Site d))}
  {a b : Site d}
-- given
  (hne : cluster d ϱ a ≠ cluster d ϱ b) :
-- imply
  Disjoint (cluster d ϱ a) (cluster d ϱ b) := by
-- proof
  apply StatMech.Percolation.bcc_cluster_disjoint_of_ne ϱ a b hne

/--
[bcc_disjoint_confining_sides](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CorridorConfinement.lean)
-/
@[path]
private lemma bcc_disjoint_confining_sides_eq
  {d : ℕ}
  {ϱ : ConfigSpace (Sym2 (Site d))}
  {a₁ a₂ a₃ : Site d}
-- given
  (hd12 : cluster d ϱ a₁ ≠ cluster d ϱ a₂)
  (hd13 : cluster d ϱ a₁ ≠ cluster d ϱ a₃)
  (hd23 : cluster d ϱ a₂ ≠ cluster d ϱ a₃) :
-- imply
  ∃ S₁ S₂ S₃ : Set (Site d), (a₁ ∈ S₁ ∧ a₂ ∈ S₂ ∧ a₃ ∈ S₃) ∧ ((∀ u v, u ∈ S₁ → (openSubgraph d ϱ).Adj u v → v ∈ S₁) ∧ (∀ u v, u ∈ S₂ → (openSubgraph d ϱ).Adj u v → v ∈ S₂) ∧ (∀ u v, u ∈ S₃ → (openSubgraph d ϱ).Adj u v → v ∈ S₃)) ∧ (Disjoint S₁ S₂ ∧ Disjoint S₁ S₃ ∧ Disjoint S₂ S₃) := by
-- proof
  apply StatMech.Percolation.bcc_disjoint_confining_sides ϱ a₁ a₂ a₃ hd12 hd13 hd23

/--
[bcc_corridorWorks_of_distinct_clusters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CorridorConfinement.lean)
-/
@[path]
private lemma bcc_corridorWorks_of_distinct_clusters_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a₁ a₂ a₃ : Site d}
  {G : Finset (Sym2 (Site d))}
-- given
  (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
  (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧ (hypercubicLattice d).Adj 0 a₃)
  (hinf : (cluster d (removeSite 0 (forceOpenFinset G ω)) a₁).Infinite ∧ (cluster d (removeSite 0 (forceOpenFinset G ω)) a₂).Infinite ∧ (cluster d (removeSite 0 (forceOpenFinset G ω)) a₃).Infinite)
  (hd12 : cluster d (removeSite 0 (forceOpenFinset G ω)) a₁ ≠ cluster d (removeSite 0 (forceOpenFinset G ω)) a₂)
  (hd13 : cluster d (removeSite 0 (forceOpenFinset G ω)) a₁ ≠ cluster d (removeSite 0 (forceOpenFinset G ω)) a₃)
  (hd23 : cluster d (removeSite 0 (forceOpenFinset G ω)) a₂ ≠ cluster d (removeSite 0 (forceOpenFinset G ω)) a₃) :
-- imply
  ω ∈ CorridorWorks a₁ a₂ a₃ G := by
-- proof
  apply StatMech.Percolation.bcc_corridorWorks_of_distinct_clusters ω a₁ a₂ a₃ G hne hadj hinf hd12 hd13 hd23

/--
[bcc_adjClosed_side_contains_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CorridorConfinement.lean)
-/
@[path]
private lemma bcc_adjClosed_side_contains_cluster_eq
  {d : ℕ}
  {ϱ : ConfigSpace (Sym2 (Site d))}
  {S : Set (Site d)}
  {a : Site d}
-- given
  (ha : a ∈ S)
  (hclosed : ∀ u v, u ∈ S → (openSubgraph d ϱ).Adj u v → v ∈ S) :
-- imply
  cluster d ϱ a ⊆ S := by
-- proof
  apply StatMech.Percolation.bcc_adjClosed_side_contains_cluster ϱ S a ha hclosed

/--
[bcc_disjoint_sides_iff_clusters_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CorridorConfinement.lean)
-/
@[path]
private lemma bcc_disjoint_sides_iff_clusters_distinct_eq
  {d : ℕ}
  {ϱ : ConfigSpace (Sym2 (Site d))}
  {a₁ a₂ a₃ : Site d} :
-- imply
  (∃ S₁ S₂ S₃ : Set (Site d), (a₁ ∈ S₁ ∧ a₂ ∈ S₂ ∧ a₃ ∈ S₃) ∧ ((∀ u v, u ∈ S₁ → (openSubgraph d ϱ).Adj u v → v ∈ S₁) ∧ (∀ u v, u ∈ S₂ → (openSubgraph d ϱ).Adj u v → v ∈ S₂) ∧ (∀ u v, u ∈ S₃ → (openSubgraph d ϱ).Adj u v → v ∈ S₃)) ∧ (Disjoint S₁ S₂ ∧ Disjoint S₁ S₃ ∧ Disjoint S₂ S₃)) ↔ (cluster d ϱ a₁ ≠ cluster d ϱ a₂ ∧ cluster d ϱ a₁ ≠ cluster d ϱ a₃ ∧ cluster d ϱ a₂ ≠ cluster d ϱ a₃) := by
-- proof
  apply StatMech.Percolation.bcc_disjoint_sides_iff_clusters_distinct ϱ a₁ a₂ a₃

/--
[bcc_axisCorridor_corridorStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CorridorConfinement.lean)
-/
@[path]
private lemma bcc_axisCorridor_corridorStep_eq
  {d : ℕ}
  {j : Fin d}
  {L : ℕ}
-- given
  (hL : 1 ≤ L) :
-- imply
  Relation.ReflTransGen (CorridorStep (hrHD_corridorEdges j L)) (hrHD_rayPt j 1) (hrHD_rayPt j (L : ℤ)) := by
-- proof
  apply StatMech.Percolation.bcc_axisCorridor_corridorStep j L hL

/--
[bcc_disjointRouting_of_corridors_and_distinct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CorridorConfinement.lean)
-/
@[path]
private lemma bcc_disjointRouting_of_corridors_and_distinct_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a₁ a₂ a₃ : Site d}
  {G : Finset (Sym2 (Site d))}
  {w₁ w₂ w₃ : Site d}
-- given
  (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
  (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧ (hypercubicLattice d).Adj 0 a₃)
  (hcor₁ : Relation.ReflTransGen (CorridorStep G) a₁ w₁)
  (hcor₂ : Relation.ReflTransGen (CorridorStep G) a₂ w₂)
  (hcor₃ : Relation.ReflTransGen (CorridorStep G) a₃ w₃)
  (hw₁ : (cluster d (removeSite 0 (forceOpenFinset G ω)) w₁).Infinite)
  (hw₂ : (cluster d (removeSite 0 (forceOpenFinset G ω)) w₂).Infinite)
  (hw₃ : (cluster d (removeSite 0 (forceOpenFinset G ω)) w₃).Infinite)
  (hd12 : cluster d (removeSite 0 (forceOpenFinset G ω)) a₁ ≠ cluster d (removeSite 0 (forceOpenFinset G ω)) a₂)
  (hd13 : cluster d (removeSite 0 (forceOpenFinset G ω)) a₁ ≠ cluster d (removeSite 0 (forceOpenFinset G ω)) a₃)
  (hd23 : cluster d (removeSite 0 (forceOpenFinset G ω)) a₂ ≠ cluster d (removeSite 0 (forceOpenFinset G ω)) a₃) :
-- imply
  DisjointCorridorRouting ω := by
-- proof
  apply StatMech.Percolation.bcc_disjointRouting_of_corridors_and_distinct ω a₁ a₂ a₃ G w₁ w₂ w₃ hne hadj hcor₁ hcor₂ hcor₃ hw₁ hw₂ hw₃ hd12 hd13 hd23

/--
[bcc_disjointRouting_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CorridorConfinement.lean)
-/
@[path]
private lemma bcc_disjointRouting_of_residue_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : bcc_distinct_clusters_residue ω) :
-- imply
  DisjointCorridorRouting ω := by
-- proof
  apply StatMech.Percolation.bcc_disjointRouting_of_residue ω h


-- created on 2026-10-23
