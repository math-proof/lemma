import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge.Part4
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[forceOpenFinset_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneMerge.lean)
-/
@[path]
private lemma forceOpenFinset_of_mem_eq
  {d : ℕ}
  {F : Finset (Sym2 (Site d))}
  {e : Sym2 (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : e ∈ F) :
-- imply
  forceOpenFinset F ω e = true := by
-- proof
  apply StatMech.Percolation.forceOpenFinset_of_mem h ω

/--
[forceOpenFinset_of_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneMerge.lean)
-/
@[path]
private lemma forceOpenFinset_of_notMem_eq
  {d : ℕ}
  {F : Finset (Sym2 (Site d))}
  {e : Sym2 (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : e ∉ F) :
-- imply
  forceOpenFinset F ω e = ω e := by
-- proof
  apply StatMech.Percolation.forceOpenFinset_of_notMem h ω

/--
[forceOpenFinset_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneMerge.lean)
-/
@[path]
private lemma forceOpenFinset_le_eq
  {d : ℕ}
  {F : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  ω ≤ forceOpenFinset F ω := by
-- proof
  apply StatMech.Percolation.forceOpenFinset_le F ω

/--
[measurable_forceOpenFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneMerge.lean)
-/
@[path]
private lemma measurable_forceOpenFinset_eq
  {d : ℕ}
  {F : Finset (Sym2 (Site d))} :
-- imply
  Measurable (fun ω : ConfigSpace (Sym2 (Site d)) => forceOpenFinset F ω) := by
-- proof
  apply StatMech.Percolation.measurable_forceOpenFinset F

/--
[openSubgraph_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneMerge.lean)
-/
@[path]
private lemma openSubgraph_mono_eq
  {d : ℕ}
  {ω ω' : ConfigSpace (Sym2 (Site d))}
-- given
  (hle : ω ≤ ω') :
-- imply
  openSubgraph d ω ≤ openSubgraph d ω' := by
-- proof
  apply StatMech.Percolation.openSubgraph_mono hle

/--
[connected_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneMerge.lean)
-/
@[path]
private lemma connected_mono_eq
  {d : ℕ}
  {ω ω' : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (hle : ω ≤ ω')
  (h : Connected d ω x y) :
-- imply
  Connected d ω' x y := by
-- proof
  apply StatMech.Percolation.connected_mono hle h

/--
[cluster_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneMerge.lean)
-/
@[path]
private lemma cluster_mono_eq
  {d : ℕ}
  {ω ω' : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hle : ω ≤ ω') :
-- imply
  cluster d ω x ⊆ cluster d ω' x := by
-- proof
  apply StatMech.Percolation.cluster_mono hle x

/--
[encard_image_lt_of_not_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneMerge.lean)
-/
@[path]
private lemma encard_image_lt_of_not_injOn_eq
  {d : ℕ}
  {s : Set α}
  {f : α → β}
-- given
  (hfin : s.Finite)
  (hni : ¬ Set.InjOn f s) :
-- imply
  (f '' s).encard < s.encard := by
-- proof
  apply StatMech.Percolation.encard_image_lt_of_not_injOn hfin hni

/--
[anchorSites_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneMerge.lean)
-/
@[path]
private lemma anchorSites_finite_eq
  {d : ℕ}
  {F : Finset (Sym2 (Site d))} :
-- imply
  (anchorSites F).Finite := by
-- proof
  apply StatMech.Percolation.anchorSites_finite F

/--
[adj_forceOpenFinset_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneMerge.lean)
-/
@[path]
private lemma adj_forceOpenFinset_cases_eq
  {d : ℕ}
  {F : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (h : (openSubgraph d (forceOpenFinset F ω)).Adj x y) :
-- imply
  (openSubgraph d ω).Adj x y ∨ (s(x, y) ∈ F) := by
-- proof
  apply StatMech.Percolation.adj_forceOpenFinset_cases F ω h

/--
[anchor_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneMerge.lean)
-/
@[path]
private lemma anchor_decomp_eq
  {d : ℕ}
  {F : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x z : Site d}
-- given
  (h : Connected d (forceOpenFinset F ω) x z) :
-- imply
  Connected d ω x z ∨ ∃ a ∈ anchorSites F, Connected d ω a z := by
-- proof
  apply StatMech.Percolation.anchor_decomp F ω x z h

/--
[exists_infinite_omega_cluster_in_D](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneMerge.lean)
-/
@[path]
private lemma exists_infinite_omega_cluster_in_D_eq
  {d : ℕ}
  {F : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (hD : (cluster d (forceOpenFinset F ω) x).Infinite) :
-- imply
  ∃ a, a ∈ cluster d (forceOpenFinset F ω) x ∧ (cluster d ω a).Infinite := by
-- proof
  apply StatMech.Percolation.exists_infinite_omega_cluster_in_D F ω x hD

/--
[forceOpen_image_repSet_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneMerge.lean)
-/
@[path]
private lemma forceOpen_image_repSet_eq_eq
  {d : ℕ}
  {F : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  (fun a => cluster d (forceOpenFinset F ω) a) '' (repSet d ω) = infiniteClusters d (forceOpenFinset F ω) := by
-- proof
  apply StatMech.Percolation.forceOpen_image_repSet_eq F ω

/--
[numInfiniteClusters_lt_of_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneMerge.lean)
-/
@[path]
private lemma numInfiniteClusters_lt_of_merge_eq
  {d : ℕ}
  {F : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (hfin : numInfiniteClusters d ω ≠ ⊤)
  (hx : (cluster d ω x).Infinite)
  (hy : (cluster d ω y).Infinite)
  (hne : cluster d ω x ≠ cluster d ω y)
  (hmerge : Connected d (forceOpenFinset F ω) x y) :
-- imply
  numInfiniteClusters d (forceOpenFinset F ω) < numInfiniteClusters d ω := by
-- proof
  apply StatMech.Percolation.numInfiniteClusters_lt_of_merge F ω hfin x y hx hy hne hmerge

/--
[mergeWitness_subset_force_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneMerge.lean)
-/
@[path]
private lemma mergeWitness_subset_force_lt_eq
  {d : ℕ}
  {F : Finset (Sym2 (Site d))}
  {k : ℕ∞}
-- given
  (hk : k ≠ ⊤) :
-- imply
  MergeWitness d F k ⊆ (fun ω => forceOpenFinset F ω) ⁻¹' {ω | numInfiniteClusters d ω < k} := by
-- proof
  apply StatMech.Percolation.mergeWitness_subset_force_lt F hk

/--
[measurableSet_numInfiniteClusters_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneMerge.lean)
-/
@[path]
private lemma measurableSet_numInfiniteClusters_lt_eq
  {d : ℕ}
  {k : ℕ∞} :
-- imply
  MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d ω < k} := by
-- proof
  apply StatMech.Percolation.measurableSet_numInfiniteClusters_lt k

/--
[numInfiniteClusters_lt_null](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneMerge.lean)
-/
@[path]
private lemma numInfiniteClusters_lt_null_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {k : ℕ∞}
-- given
  (hk : μ {ω | numInfiniteClusters d ω = k} = 1) :
-- imply
  μ {ω | numInfiniteClusters d ω < k} = 0 := by
-- proof
  apply StatMech.Percolation.numInfiniteClusters_lt_null μ hk

/--
[merge_contradiction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneMerge.lean)
-/
@[path]
private lemma merge_contradiction_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {k : ℕ∞}
  {F : Finset (Sym2 (Site d))}
  {A : Set (ConfigSpace (Sym2 (Site d)))}
-- given
  (hk : μ {ω | numInfiniteClusters d ω = k} = 1)
  (hfe : (μ.map (fun ω => forceOpenFinset F ω)) ≪ μ)
  (hApos : 0 < μ A)
  (hAsub : A ⊆ (fun ω => forceOpenFinset F ω) ⁻¹' {ω | numInfiniteClusters d ω < k}) :
-- imply
  False := by
-- proof
  apply StatMech.Percolation.merge_contradiction μ hk F hfe hApos hAsub

/--
[burton_keane_merge_excludes_finite_ge_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneMerge.lean)
-/
@[path]
private lemma burton_keane_merge_excludes_finite_ge_two_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hmergeGeom : ∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters d ω = k} = 1 → ∃ F : Finset (Sym2 (Site d)), 0 < μ (MergeWitness d F k)) :
-- imply
  ∀ k : ℕ∞, μ {ω | numInfiniteClusters d ω = k} = 1 → 2 ≤ k → k = ⊤ := by
-- proof
  apply StatMech.Percolation.burton_keane_merge_excludes_finite_ge_two μ hfe hmergeGeom

/--
[merge_event_null](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneMerge.lean)
-/
@[path]
private lemma merge_event_null_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hkne_top : ∀ k : ℕ∞, μ {ω | numInfiniteClusters d ω = k} = 1 → k ≠ ⊤)
  (hmergeGeom : ∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters d ω = k} = 1 → ∃ F : Finset (Sym2 (Site d)), 0 < μ (MergeWitness d F k)) :
-- imply
  μ (atLeastTwoInfinite d) = 0 := by
-- proof
  apply StatMech.Percolation.merge_event_null μ herg hfe hkne_top hmergeGeom

/--
[burton_keane_uniqueness_via_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneMerge.lean)
-/
@[path]
private lemma burton_keane_uniqueness_via_merge_eq
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
  (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} → 0 < μ {ω | IsTrifurcation d ω 0})
  (hmergeGeom : ∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters d ω = k} = 1 → ∃ F : Finset (Sym2 (Site d)), 0 < μ (MergeWitness d F k)) :
-- imply
  (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.burton_keane_uniqueness_via_merge μ herg hfe bdry hbound hvol hdens htrif hmergeGeom


-- created on 2026-10-23
