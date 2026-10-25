import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentTraceCanonicalRouting.Part4
open MeasureTheory Set StatMech StatMech.FrontierB


/--
[latticeEdgePart_subset_edgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCanonicalRouting.lean)
-/
@[path]
private lemma latticeEdgePart_subset_edgeSet_eq
  {d : ℕ}
  {G : Finset (Sym2 (Site d))} :
-- imply
  (↑(latticeEdgePart d G) : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet := by
-- proof
  apply StatMech.FrontierB.latticeEdgePart_subset_edgeSet G

/--
[forceOpenFinset_latticeEdgePart_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCanonicalRouting.lean)
-/
@[path]
private lemma forceOpenFinset_latticeEdgePart_apply_eq
  {d : ℕ}
  {G : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
  {e : Sym2 (Site d)}
-- given
  (he : e ∈ (hypercubicLattice d).edgeSet) :
-- imply
  forceOpenFinset (latticeEdgePart d G) ω e = forceOpenFinset G ω e := by
-- proof
  apply StatMech.FrontierB.forceOpenFinset_latticeEdgePart_apply G ω he

/--
[corridorStep_latticeEdgePart_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCanonicalRouting.lean)
-/
@[path]
private lemma corridorStep_latticeEdgePart_iff_eq
  {d : ℕ}
  {G : Finset (Sym2 (Site d))}
  {x y : Site d} :
-- imply
  CorridorStep (latticeEdgePart d G) x y ↔ CorridorStep G x y := by
-- proof
  apply StatMech.FrontierB.corridorStep_latticeEdgePart_iff G x y

/--
[corridor_latticeEdgePart_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCanonicalRouting.lean)
-/
@[path]
private lemma corridor_latticeEdgePart_iff_eq
  {d : ℕ}
  {G : Finset (Sym2 (Site d))}
  {x y : Site d} :
-- imply
  Relation.ReflTransGen (CorridorStep (latticeEdgePart d G)) x y ↔ Relation.ReflTransGen (CorridorStep G) x y := by
-- proof
  apply StatMech.FrontierB.corridor_latticeEdgePart_iff G x y

/--
[openSubgraph_forceOpenFinset_latticeEdgePart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCanonicalRouting.lean)
-/
@[path]
private lemma openSubgraph_forceOpenFinset_latticeEdgePart_eq
  {d : ℕ}
  {G : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  openSubgraph d (forceOpenFinset (latticeEdgePart d G) ω) = openSubgraph d (forceOpenFinset G ω) := by
-- proof
  apply StatMech.FrontierB.openSubgraph_forceOpenFinset_latticeEdgePart G ω

/--
[removeSite_forceOpenFinset_latticeEdgePart_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCanonicalRouting.lean)
-/
@[path]
private lemma removeSite_forceOpenFinset_latticeEdgePart_apply_eq
  {d : ℕ}
  {z : Site d}
  {G : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
  {e : Sym2 (Site d)}
-- given
  (he : e ∈ (hypercubicLattice d).edgeSet) :
-- imply
  removeSite z (forceOpenFinset (latticeEdgePart d G) ω) e = removeSite z (forceOpenFinset G ω) e := by
-- proof
  apply StatMech.FrontierB.removeSite_forceOpenFinset_latticeEdgePart_apply z G ω he

/--
[openSubgraph_removeSite_forceOpenFinset_latticeEdgePart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCanonicalRouting.lean)
-/
@[path]
private lemma openSubgraph_removeSite_forceOpenFinset_latticeEdgePart_eq
  {d : ℕ}
  {z : Site d}
  {G : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  openSubgraph d (removeSite z (forceOpenFinset (latticeEdgePart d G) ω)) = openSubgraph d (removeSite z (forceOpenFinset G ω)) := by
-- proof
  apply StatMech.FrontierB.openSubgraph_removeSite_forceOpenFinset_latticeEdgePart z G ω

/--
[cluster_removeSite_forceOpenFinset_latticeEdgePart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCanonicalRouting.lean)
-/
@[path]
private lemma cluster_removeSite_forceOpenFinset_latticeEdgePart_eq
  {d : ℕ}
  {z x : Site d}
  {G : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  cluster d (removeSite z (forceOpenFinset (latticeEdgePart d G) ω)) x = cluster d (removeSite z (forceOpenFinset G ω)) x := by
-- proof
  apply StatMech.FrontierB.cluster_removeSite_forceOpenFinset_latticeEdgePart z x G ω

/--
[corridorWorks_latticeEdgePart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCanonicalRouting.lean)
-/
@[path]
private lemma corridorWorks_latticeEdgePart_eq
  {d : ℕ}
  {a₁ a₂ a₃ : Site d}
  {G : Finset (Sym2 (Site d))} :
-- imply
  CorridorWorks a₁ a₂ a₃ (latticeEdgePart d G) = CorridorWorks a₁ a₂ a₃ G := by
-- proof
  apply StatMech.FrontierB.corridorWorks_latticeEdgePart a₁ a₂ a₃ G

/--
[not_mengerCore_of_originNeighborsCutConnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCanonicalRouting.lean)
-/
@[path]
private lemma not_mengerCore_of_originNeighborsCutConnected_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hconn : OriginNeighborsCutConnected ω) :
-- imply
  ¬ MengerCore ω := by
-- proof
  apply StatMech.FrontierB.not_mengerCore_of_originNeighborsCutConnected ω hconn

/--
[hubCorridorWorks_latticeEdgePart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCanonicalRouting.lean)
-/
@[path]
private lemma hubCorridorWorks_latticeEdgePart_eq
  {d : ℕ}
  {z a₁ a₂ a₃ : Site d}
  {G : Finset (Sym2 (Site d))} :
-- imply
  HubCorridorWorks z a₁ a₂ a₃ (latticeEdgePart d G) = HubCorridorWorks z a₁ a₂ a₃ G := by
-- proof
  apply StatMech.FrontierB.hubCorridorWorks_latticeEdgePart z a₁ a₂ a₃ G

/--
[hubTripleEdges_subset_edgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCanonicalRouting.lean)
-/
@[path]
private lemma hubTripleEdges_subset_edgeSet_eq
  {d : ℕ}
  {z a₁ a₂ a₃ : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj z a₁ ∧ (hypercubicLattice d).Adj z a₂ ∧ (hypercubicLattice d).Adj z a₃) :
-- imply
  (↑(hubTripleEdges z a₁ a₂ a₃) : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet := by
-- proof
  apply StatMech.FrontierB.hubTripleEdges_subset_edgeSet z a₁ a₂ a₃ hadj

/--
[hubCombinedEdges_subset_edgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCanonicalRouting.lean)
-/
@[path]
private lemma hubCombinedEdges_subset_edgeSet_eq
  {d : ℕ}
  {z a₁ a₂ a₃ : Site d}
  {G : Finset (Sym2 (Site d))}
-- given
  (hadj : (hypercubicLattice d).Adj z a₁ ∧ (hypercubicLattice d).Adj z a₂ ∧ (hypercubicLattice d).Adj z a₃) :
-- imply
  (↑(hubTripleEdges z a₁ a₂ a₃ ∪ latticeEdgePart d G) : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet := by
-- proof
  apply StatMech.FrontierB.hubCombinedEdges_subset_edgeSet z a₁ a₂ a₃ G hadj

/--
[isCanonicalTrifurcation_of_neighbors_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCanonicalRouting.lean)
-/
@[path]
private lemma isCanonicalTrifurcation_of_neighbors_at_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {z a₁ a₂ a₃ : Site d}
-- given
  (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
  (hadj : (hypercubicLattice d).Adj z a₁ ∧ (hypercubicLattice d).Adj z a₂ ∧ (hypercubicLattice d).Adj z a₃)
  (hinf : (cluster d (removeSite z ω) a₁).Infinite ∧ (cluster d (removeSite z ω) a₂).Infinite ∧ (cluster d (removeSite z ω) a₃).Infinite)
  (hsep : ¬ Connected d (removeSite z ω) a₁ a₂ ∧ ¬ Connected d (removeSite z ω) a₁ a₃ ∧ ¬ Connected d (removeSite z ω) a₂ a₃) :
-- imply
  IsCanonicalTrifurcation d (forceOpenFinset (hubTripleEdges z a₁ a₂ a₃) ω) z := by
-- proof
  apply StatMech.FrontierB.isCanonicalTrifurcation_of_neighbors_at ω z a₁ a₂ a₃ hne hadj hinf hsep

/--
[hubCorridorWorks_subset_force_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCanonicalRouting.lean)
-/
@[path]
private lemma hubCorridorWorks_subset_force_canonical_eq
  {d : ℕ}
  {z a₁ a₂ a₃ : Site d}
  {G : Finset (Sym2 (Site d))} :
-- imply
  HubCorridorWorks z a₁ a₂ a₃ G ⊆ (fun ω => forceOpenFinset (hubTripleEdges z a₁ a₂ a₃ ∪ G) ω) ⁻¹' {ω | IsCanonicalTrifurcation d ω z} := by
-- proof
  apply StatMech.FrontierB.hubCorridorWorks_subset_force_canonical z a₁ a₂ a₃ G

/--
[pos_of_lattice_forceOpen_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCanonicalRouting.lean)
-/
@[path]
private lemma pos_of_lattice_forceOpen_preimage_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  {F : Finset (Sym2 (Site d))}
  {A B : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (hfe : HasLatticeFiniteEnergyMerge μ)
  (hFL : (↑F : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet)
  (hmB : MeasurableSet B)
  (hsub : A ⊆ (fun ω => forceOpenFinset F ω) ⁻¹' B)
  (hApos : 0 < μ A) :
-- imply
  0 < μ B := by
-- proof
  apply StatMech.FrontierB.pos_of_lattice_forceOpen_preimage μ hfe F hFL hmB hsub hApos

/--
[canonicalTrifurcation_pos_of_variableHubCorridorCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCanonicalRouting.lean)
-/
@[path]
private lemma canonicalTrifurcation_pos_of_variableHubCorridorCover_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {n : ℕ}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hfe : HasLatticeFiniteEnergyMerge μ)
  (hcover : threeMeetBox d n ⊆ ⋃ (z : Site d) (a₁ : Site d) (a₂ : Site d) (a₃ : Site d) (G : Finset (Sym2 (Site d))), HubCorridorWorks z a₁ a₂ a₃ G)
  (hpos : 0 < μ (threeMeetBox d n)) :
-- imply
  0 < μ {ω | IsCanonicalTrifurcation d ω 0} := by
-- proof
  apply StatMech.FrontierB.canonicalTrifurcation_pos_of_variableHubCorridorCover μ hinv hfe hcover hpos

/--
[canonicalTrifurcation_pos_of_variableHubCorridorCovers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCanonicalRouting.lean)
-/
@[path]
private lemma canonicalTrifurcation_pos_of_variableHubCorridorCovers_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hfe : HasLatticeFiniteEnergyMerge μ)
  (hcover : ∀ n : ℕ, threeMeetBox d n ⊆ ⋃ (z : Site d) (a₁ : Site d) (a₂ : Site d) (a₃ : Site d) (G : Finset (Sym2 (Site d))), HubCorridorWorks z a₁ a₂ a₃ G)
  (htop : 0 < μ {ω | numInfiniteClusters d ω = ⊤}) :
-- imply
  0 < μ {ω | IsCanonicalTrifurcation d ω 0} := by
-- proof
  apply StatMech.FrontierB.canonicalTrifurcation_pos_of_variableHubCorridorCovers μ hinv hfe hcover htop

/--
[originTripleEdges_subset_edgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCanonicalRouting.lean)
-/
@[path]
private lemma originTripleEdges_subset_edgeSet_eq
  {d : ℕ}
  {a₁ a₂ a₃ : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧ (hypercubicLattice d).Adj 0 a₃) :
-- imply
  (↑({s((0 : Site d), a₁), s((0 : Site d), a₂), s((0 : Site d), a₃)} : Finset (Sym2 (Site d))) : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet := by
-- proof
  apply StatMech.FrontierB.originTripleEdges_subset_edgeSet a₁ a₂ a₃ hadj

/--
[isCanonicalTrifurcation_of_neighbors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCanonicalRouting.lean)
-/
@[path]
private lemma isCanonicalTrifurcation_of_neighbors_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a₁ a₂ a₃ : Site d}
-- given
  (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
  (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧ (hypercubicLattice d).Adj 0 a₃)
  (hinf : (cluster d (removeSite 0 ω) a₁).Infinite ∧ (cluster d (removeSite 0 ω) a₂).Infinite ∧ (cluster d (removeSite 0 ω) a₃).Infinite)
  (hsep : ¬ Connected d (removeSite 0 ω) a₁ a₂ ∧ ¬ Connected d (removeSite 0 ω) a₁ a₃ ∧ ¬ Connected d (removeSite 0 ω) a₂ a₃) :
-- imply
  IsCanonicalTrifurcation d (forceOpenFinset {s((0 : Site d), a₁), s((0 : Site d), a₂), s((0 : Site d), a₃)} ω) 0 := by
-- proof
  apply StatMech.FrontierB.isCanonicalTrifurcation_of_neighbors ω a₁ a₂ a₃ hne hadj hinf hsep

/--
[precursor_subset_force_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCanonicalRouting.lean)
-/
@[path]
private lemma precursor_subset_force_canonical_eq
  {d : ℕ}
  {a₁ a₂ a₃ : Site d} :
-- imply
  NeighborTrifPrecursor d a₁ a₂ a₃ ⊆ (fun ω => forceOpenFinset {s((0 : Site d), a₁), s((0 : Site d), a₂), s((0 : Site d), a₃)} ω) ⁻¹' {ω | IsCanonicalTrifurcation d ω 0} := by
-- proof
  apply StatMech.FrontierB.precursor_subset_force_canonical a₁ a₂ a₃

/--
[canonicalTrifurcation_pos_of_precursor_lattice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCanonicalRouting.lean)
-/
@[path]
private lemma canonicalTrifurcation_pos_of_precursor_lattice_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {a₁ a₂ a₃ : Site d}
-- given
  (hfe : HasLatticeFiniteEnergyMerge μ)
  (hpos : 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃)) :
-- imply
  0 < μ {ω | IsCanonicalTrifurcation d ω 0} := by
-- proof
  apply StatMech.FrontierB.canonicalTrifurcation_pos_of_precursor_lattice μ hfe a₁ a₂ a₃ hpos


-- created on 2026-10-23
