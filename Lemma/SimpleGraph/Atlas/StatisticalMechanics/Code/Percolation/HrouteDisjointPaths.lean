import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.HrouteDisjointPaths
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation StatMech.Percolation.DisjointPaths


/--
[isOpenEdge_removeSite_forceOpen_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteDisjointPaths.lean)
-/
@[path]
private lemma isOpenEdge_removeSite_forceOpen_step_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))}
  {x y : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj x y)
  (hmem : s(x, y) ∈ G)
  (h0 : (0 : Site d) ∉ s(x, y)) :
-- imply
  IsOpenEdge d (removeSite 0 (forceOpenFinset G ω)) x y := by
-- proof
  apply StatMech.Percolation.DisjointPaths.isOpenEdge_removeSite_forceOpen_step ω G hadj hmem h0

/--
[connected_removeSite_forceOpen_of_corridor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteDisjointPaths.lean)
-/
@[path]
private lemma connected_removeSite_forceOpen_of_corridor_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {G : Finset (Sym2 (Site d))}
  {p q : Site d}
-- given
  (h : Relation.ReflTransGen (fun u v => (hypercubicLattice d).Adj u v ∧ s(u, v) ∈ G ∧ (0 : Site d) ∉ s(u, v)) p q) :
-- imply
  Connected d (removeSite 0 (forceOpenFinset G ω)) p q := by
-- proof
  apply StatMech.Percolation.DisjointPaths.connected_removeSite_forceOpen_of_corridor ω G h

/--
[corridorWorks_subset_force_precursor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteDisjointPaths.lean)
-/
@[path]
private lemma corridorWorks_subset_force_precursor_eq
  {d : ℕ}
  {a₁ a₂ a₃ : Site d}
  {G : Finset (Sym2 (Site d))} :
-- imply
  CorridorWorks a₁ a₂ a₃ G ⊆ (fun ω => forceOpenFinset G ω) ⁻¹' NeighborTrifPrecursor d a₁ a₂ a₃ := by
-- proof
  apply StatMech.Percolation.DisjointPaths.corridorWorks_subset_force_precursor a₁ a₂ a₃ G

/--
[cluster_subset_of_adjClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteDisjointPaths.lean)
-/
@[path]
private lemma cluster_subset_of_adjClosed_eq
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
  apply StatMech.Percolation.DisjointPaths.cluster_subset_of_adjClosed ϱ S a ha hclosed

/--
[cluster_ne_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteDisjointPaths.lean)
-/
@[path]
private lemma cluster_ne_of_disjoint_eq
  {d : ℕ}
  {ϱ : ConfigSpace (Sym2 (Site d))}
  {a b : Site d}
  {S T : Set (Site d)}
-- given
  (hS : cluster d ϱ a ⊆ S)
  (hT : cluster d ϱ b ⊆ T)
  (hdisj : Disjoint S T) :
-- imply
  cluster d ϱ a ≠ cluster d ϱ b := by
-- proof
  apply StatMech.Percolation.DisjointPaths.cluster_ne_of_disjoint ϱ a b S T hS hT hdisj

/--
[corridorWorks_of_separated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteDisjointPaths.lean)
-/
@[path]
private lemma corridorWorks_of_separated_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a₁ a₂ a₃ : Site d}
  {G : Finset (Sym2 (Site d))}
  {S₁ S₂ S₃ : Set (Site d)}
-- given
  (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
  (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧ (hypercubicLattice d).Adj 0 a₃)
  (hmem₁ : a₁ ∈ S₁)
  (hmem₂ : a₂ ∈ S₂)
  (hmem₃ : a₃ ∈ S₃)
  (hcl₁ : ∀ u v, u ∈ S₁ → (openSubgraph d (removeSite 0 (forceOpenFinset G ω))).Adj u v → v ∈ S₁)
  (hcl₂ : ∀ u v, u ∈ S₂ → (openSubgraph d (removeSite 0 (forceOpenFinset G ω))).Adj u v → v ∈ S₂)
  (hcl₃ : ∀ u v, u ∈ S₃ → (openSubgraph d (removeSite 0 (forceOpenFinset G ω))).Adj u v → v ∈ S₃)
  (hd12 : Disjoint S₁ S₂)
  (hd13 : Disjoint S₁ S₃)
  (hd23 : Disjoint S₂ S₃)
  (hinf : (cluster d (removeSite 0 (forceOpenFinset G ω)) a₁).Infinite ∧ (cluster d (removeSite 0 (forceOpenFinset G ω)) a₂).Infinite ∧ (cluster d (removeSite 0 (forceOpenFinset G ω)) a₃).Infinite) :
-- imply
  ω ∈ CorridorWorks a₁ a₂ a₃ G := by
-- proof
  apply StatMech.Percolation.DisjointPaths.corridorWorks_of_separated ω a₁ a₂ a₃ G hne hadj S₁ S₂ S₃ hmem₁ hmem₂ hmem₃ hcl₁ hcl₂ hcl₃ hd12 hd13 hd23 hinf

/--
[corridorWorks_of_corridors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteDisjointPaths.lean)
-/
@[path]
private lemma corridorWorks_of_corridors_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a₁ a₂ a₃ : Site d}
  {G : Finset (Sym2 (Site d))}
  {w₁ w₂ w₃ : Site d}
  {S₁ S₂ S₃ : Set (Site d)}
-- given
  (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
  (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧ (hypercubicLattice d).Adj 0 a₃)
  (hcor₁ : Relation.ReflTransGen (CorridorStep G) a₁ w₁)
  (hcor₂ : Relation.ReflTransGen (CorridorStep G) a₂ w₂)
  (hcor₃ : Relation.ReflTransGen (CorridorStep G) a₃ w₃)
  (hw₁ : (cluster d (removeSite 0 (forceOpenFinset G ω)) w₁).Infinite)
  (hw₂ : (cluster d (removeSite 0 (forceOpenFinset G ω)) w₂).Infinite)
  (hw₃ : (cluster d (removeSite 0 (forceOpenFinset G ω)) w₃).Infinite)
  (hmem₁ : a₁ ∈ S₁)
  (hmem₂ : a₂ ∈ S₂)
  (hmem₃ : a₃ ∈ S₃)
  (hcl₁ : ∀ u v, u ∈ S₁ → (openSubgraph d (removeSite 0 (forceOpenFinset G ω))).Adj u v → v ∈ S₁)
  (hcl₂ : ∀ u v, u ∈ S₂ → (openSubgraph d (removeSite 0 (forceOpenFinset G ω))).Adj u v → v ∈ S₂)
  (hcl₃ : ∀ u v, u ∈ S₃ → (openSubgraph d (removeSite 0 (forceOpenFinset G ω))).Adj u v → v ∈ S₃)
  (hd12 : Disjoint S₁ S₂)
  (hd13 : Disjoint S₁ S₃)
  (hd23 : Disjoint S₂ S₃) :
-- imply
  ω ∈ CorridorWorks a₁ a₂ a₃ G := by
-- proof
  apply StatMech.Percolation.DisjointPaths.corridorWorks_of_corridors ω a₁ a₂ a₃ G hne hadj w₁ w₂ w₃ hcor₁ hcor₂ hcor₃ hw₁ hw₂ hw₃ S₁ S₂ S₃ hmem₁ hmem₂ hmem₃ hcl₁ hcl₂ hcl₃ hd12 hd13 hd23

/--
[measurableSet_clusterInfinite_removeSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteDisjointPaths.lean)
-/
@[path]
private lemma measurableSet_clusterInfinite_removeSite_eq
  {d : ℕ}
  {x a : Site d} :
-- imply
  MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | (cluster d (removeSite x ω) a).Infinite} := by
-- proof
  apply StatMech.Percolation.DisjointPaths.measurableSet_clusterInfinite_removeSite x a

/--
[measurableSet_neighborTrifPrecursor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteDisjointPaths.lean)
-/
@[path]
private lemma measurableSet_neighborTrifPrecursor_eq
  {d : ℕ}
  {a₁ a₂ a₃ : Site d} :
-- imply
  MeasurableSet (NeighborTrifPrecursor d a₁ a₂ a₃) := by
-- proof
  apply StatMech.Percolation.DisjointPaths.measurableSet_neighborTrifPrecursor a₁ a₂ a₃

/--
[exists_pos_of_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteDisjointPaths.lean)
-/
@[path]
private lemma exists_pos_of_cover_eq
  {d : ℕ}
  [Countable ι]
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {A : Set (ConfigSpace (Sym2 (Site d)))}
  {B : ι → Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (hsub : A ⊆ ⋃ i, B i)
  (hApos : 0 < μ A) :
-- imply
  ∃ i, 0 < μ (B i) := by
-- proof
  apply StatMech.Percolation.DisjointPaths.exists_pos_of_cover μ hsub hApos

/--
[pos_of_forceOpen_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteDisjointPaths.lean)
-/
@[path]
private lemma pos_of_forceOpen_preimage_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {G : Finset (Sym2 (Site d))}
  {A B : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hmB : MeasurableSet B)
  (hsub : A ⊆ (fun ω => forceOpenFinset G ω) ⁻¹' B)
  (hApos : 0 < μ A) :
-- imply
  0 < μ B := by
-- proof
  apply StatMech.Percolation.DisjointPaths.pos_of_forceOpen_preimage μ hfe G hmB hsub hApos

/--
[hroute_at_of_corridorCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteDisjointPaths.lean)
-/
@[path]
private lemma hroute_at_of_corridorCover_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {n : ℕ}
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hcorr : threeMeetBox d n ⊆ ⋃ (a₁ : Site d) (a₂ : Site d) (a₃ : Site d) (G : Finset (Sym2 (Site d))), CorridorWorks a₁ a₂ a₃ G)
  (hpos : 0 < μ (threeMeetBox d n)) :
-- imply
  ∃ a₁ a₂ a₃ : Site d, 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃) := by
-- proof
  apply StatMech.Percolation.DisjointPaths.hroute_at_of_corridorCover μ hfe hcorr hpos

/--
[hroute_of_corridorCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteDisjointPaths.lean)
-/
@[path]
private lemma hroute_of_corridorCover_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hcorr : ∀ n : ℕ, threeMeetBox d n ⊆ ⋃ (a₁ : Site d) (a₂ : Site d) (a₃ : Site d) (G : Finset (Sym2 (Site d))), CorridorWorks a₁ a₂ a₃ G) :
-- imply
  ∀ n : ℕ, 0 < μ (threeMeetBox d n) → ∃ a₁ a₂ a₃ : Site d, 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃) := by
-- proof
  apply StatMech.Percolation.DisjointPaths.hroute_of_corridorCover μ hfe hcorr

/--
[corridorCover_of_routing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteDisjointPaths.lean)
-/
@[path]
private lemma corridorCover_of_routing_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (hroute : ∀ ω ∈ threeMeetBox d n, DisjointCorridorRouting ω) :
-- imply
  threeMeetBox d n ⊆ ⋃ (a₁ : Site d) (a₂ : Site d) (a₃ : Site d) (G : Finset (Sym2 (Site d))), CorridorWorks a₁ a₂ a₃ G := by
-- proof
  apply StatMech.Percolation.DisjointPaths.corridorCover_of_routing hroute

/--
[burton_keane_uniqueness_corridorCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteDisjointPaths.lean)
-/
@[path]
private lemma burton_keane_uniqueness_corridorCover_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {bdry : ℕ → ℕ}
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
  (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
  (hdens : Filter.Tendsto (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ)) Filter.atTop (nhds 0))
  (hcorr : ∀ n : ℕ, threeMeetBox d n ⊆ ⋃ (a₁ : Site d) (a₂ : Site d) (a₃ : Site d) (G : Finset (Sym2 (Site d))), CorridorWorks a₁ a₂ a₃ G) :
-- imply
  (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.DisjointPaths.burton_keane_uniqueness_corridorCover μ herg hfe bdry hbound hvol hdens hcorr

/--
[burton_keane_uniqueness_disjointRouting](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteDisjointPaths.lean)
-/
@[path]
private lemma burton_keane_uniqueness_disjointRouting_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {bdry : ℕ → ℕ}
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
  (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
  (hdens : Filter.Tendsto (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ)) Filter.atTop (nhds 0))
  (hroute : ∀ (n : ℕ) (ω : ConfigSpace (Sym2 (Site d))), ω ∈ threeMeetBox d n → DisjointCorridorRouting ω) :
-- imply
  (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.DisjointPaths.burton_keane_uniqueness_disjointRouting μ herg hfe bdry hbound hvol hdens hroute


-- created on 2026-10-23
