import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc48classical.Part3
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc48_mem_classicalTrifFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc48classical.lean)
-/
@[path]
private lemma bc48_mem_classicalTrifFinset_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Site d} :
-- imply
  x ∈ bc48_classicalTrifFinset ω n ↔ x ∈ box d n ∧ bc47_IsClassicalTrifurcation ω x := by
-- proof
  apply StatMech.Walls.bc48_mem_classicalTrifFinset

/--
[bc48_Tcount_classical_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc48classical.lean)
-/
@[path]
private lemma bc48_Tcount_classical_eq_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  bc48_Tcount_classical d ω n = (bc48_classicalTrifFinset ω n).card := by
-- proof
  apply StatMech.Walls.bc48_Tcount_classical_eq ω n

/--
[bc48_classicalTrifFinset_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc48classical.lean)
-/
@[path]
private lemma bc48_classicalTrifFinset_subset_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  bc48_classicalTrifFinset ω n ⊆ tfc_trifFinset ω n := by
-- proof
  apply StatMech.Walls.bc48_classicalTrifFinset_subset ω n

/--
[bc48_Tcount_classical_le_Tcount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc48classical.lean)
-/
@[path]
private lemma bc48_Tcount_classical_le_Tcount_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  bc48_Tcount_classical d ω n ≤ Tcount d ω n := by
-- proof
  apply StatMech.Walls.bc48_Tcount_classical_le_Tcount ω n

/--
[bc48_classical_reaches_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc48classical.lean)
-/
@[path]
private lemma bc48_classical_reaches_boundary_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Site d}
-- given
  (hxbox : x ∈ box d n)
  (hcl : bc47_IsClassicalTrifurcation ω x) :
-- imply
  ∃ a₁ a₂ a₃ : Site d, (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧ ((openSubgraph d ω).Adj x a₁ ∧ (openSubgraph d ω).Adj x a₂ ∧ (openSubgraph d ω).Adj x a₃) ∧ (¬ Connected d (removeSite x ω) a₁ a₂ ∧ ¬ Connected d (removeSite x ω) a₁ a₃ ∧ ¬ Connected d (removeSite x ω) a₂ a₃) ∧ (∃ z₁ ∈ vertexBoundary d (n + 1), Connected d (removeSite x ω) a₁ z₁) ∧ (∃ z₂ ∈ vertexBoundary d (n + 1), Connected d (removeSite x ω) a₂ z₂) ∧ (∃ z₃ ∈ vertexBoundary d (n + 1), Connected d (removeSite x ω) a₃ z₃) := by
-- proof
  apply StatMech.Walls.bc48_classical_reaches_boundary ω n x hxbox hcl

/--
[bc48_Tcount_classical_le_boundary_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc48classical.lean)
-/
@[path]
private lemma bc48_Tcount_classical_le_boundary_of_residue_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bc48_ClassicalBoundaryArmInjection ω n) :
-- imply
  bc48_Tcount_classical d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc48_Tcount_classical_le_boundary_of_residue ω n h

/--
[bc48_Tcount_classical_le_boundary_of_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc48classical.lean)
-/
@[path]
private lemma bc48_Tcount_classical_le_boundary_of_injection_eq
  {d : ℕ}
-- given
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), bc48_ClassicalBoundaryArmInjection ω n) :
-- imply
  ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), bc48_Tcount_classical d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Walls.bc48_Tcount_classical_le_boundary_of_injection hres

/--
[bc48_isOpenEdge_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc48classical.lean)
-/
@[path]
private lemma bc48_isOpenEdge_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d} :
-- imply
  IsOpenEdge d (shift g ω) (g • x) (g • y) ↔ IsOpenEdge d ω x y := by
-- proof
  apply StatMech.Walls.bc48_isOpenEdge_shift g ω x y

/--
[bc48_isClassicalTrif_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc48classical.lean)
-/
@[path]
private lemma bc48_isClassicalTrif_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d} :
-- imply
  bc47_IsClassicalTrifurcation (shift g ω) (g • x) ↔ bc47_IsClassicalTrifurcation ω x := by
-- proof
  apply StatMech.Walls.bc48_isClassicalTrif_shift g ω x

/--
[bc48_measurableSet_clusterInfinite_removeSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc48classical.lean)
-/
@[path]
private lemma bc48_measurableSet_clusterInfinite_removeSite_eq
  {d : ℕ}
  {x a : Site d} :
-- imply
  MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | (cluster d (removeSite x ω) a).Infinite} := by
-- proof
  apply StatMech.Walls.bc48_measurableSet_clusterInfinite_removeSite x a

/--
[bc48_measurableSet_isOpenEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc48classical.lean)
-/
@[path]
private lemma bc48_measurableSet_isOpenEdge_eq
  {d : ℕ}
  {x a : Site d} :
-- imply
  MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | IsOpenEdge d ω x a} := by
-- proof
  apply StatMech.Walls.bc48_measurableSet_isOpenEdge x a

/--
[bc48_measurableSet_isClassicalTrifurcation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc48classical.lean)
-/
@[path]
private lemma bc48_measurableSet_isClassicalTrifurcation_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | bc47_IsClassicalTrifurcation ω x} := by
-- proof
  apply StatMech.Walls.bc48_measurableSet_isClassicalTrifurcation x

/--
[bc48_classicalTrifProb_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc48classical.lean)
-/
@[path]
private lemma bc48_classicalTrifProb_const_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  {x : Site d}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
-- imply
  μ {ω | bc47_IsClassicalTrifurcation ω x} = μ {ω | bc47_IsClassicalTrifurcation ω 0} := by
-- proof
  apply StatMech.Walls.bc48_classicalTrifProb_const μ hinv x

/--
[bc48_Tcount_classical_eq_sum_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc48classical.lean)
-/
@[path]
private lemma bc48_Tcount_classical_eq_sum_indicator_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  (bc48_Tcount_classical d ω n : ℝ≥0∞) = ∑ x ∈ boxFinsetBK d n, ({ω' | bc47_IsClassicalTrifurcation ω' x}.indicator (fun _ => (1 : ℝ≥0∞))) ω := by
-- proof
  apply StatMech.Walls.bc48_Tcount_classical_eq_sum_indicator ω n

/--
[bc48_expected_Tcount_classical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc48classical.lean)
-/
@[path]
private lemma bc48_expected_Tcount_classical_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  {n : ℕ}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
-- imply
  ∫⁻ ω, (bc48_Tcount_classical d ω n : ℝ≥0∞) ∂μ = (boxFinsetBK d n).card • μ {ω | bc47_IsClassicalTrifurcation ω 0} := by
-- proof
  apply StatMech.Walls.bc48_expected_Tcount_classical μ hinv n

/--
[bc48_classicalTrif_prob_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc48classical.lean)
-/
@[path]
private lemma bc48_classicalTrif_prob_eq_zero_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {bdry : ℕ → ℕ}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), bc48_Tcount_classical d ω n ≤ bdry n)
  (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
  (hdens : Filter.Tendsto (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ)) Filter.atTop (nhds 0)) :
-- imply
  μ {ω | bc47_IsClassicalTrifurcation ω 0} = 0 := by
-- proof
  apply StatMech.Walls.bc48_classicalTrif_prob_eq_zero μ hinv bdry hbound hvol hdens

/--
[bc48_numInfiniteClusters_ae_const_ne_top_classical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc48classical.lean)
-/
@[path]
private lemma bc48_numInfiniteClusters_ae_const_ne_top_classical_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {bdry : ℕ → ℕ}
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), bc48_Tcount_classical d ω n ≤ bdry n)
  (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
  (hdens : Filter.Tendsto (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ)) Filter.atTop (nhds 0))
  (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} → 0 < μ {ω | bc47_IsClassicalTrifurcation ω 0}) :
-- imply
  ∃ k : ℕ∞, k ≠ ⊤ ∧ μ {ω | numInfiniteClusters d ω = k} = 1 := by
-- proof
  apply StatMech.Walls.bc48_numInfiniteClusters_ae_const_ne_top_classical μ herg bdry hbound hvol hdens htrif

/--
[bc48_kne_top_classical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc48classical.lean)
-/
@[path]
private lemma bc48_kne_top_classical_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {bdry : ℕ → ℕ}
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), bc48_Tcount_classical d ω n ≤ bdry n)
  (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
  (hdens : Filter.Tendsto (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ)) Filter.atTop (nhds 0))
  (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} → 0 < μ {ω | bc47_IsClassicalTrifurcation ω 0}) :
-- imply
  ∀ k : ℕ∞, μ {ω | numInfiniteClusters d ω = k} = 1 → k ≠ ⊤ := by
-- proof
  apply StatMech.Walls.bc48_kne_top_classical μ herg bdry hbound hvol hdens htrif

/--
[bc48_burton_keane_uniqueness_via_merge_classical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc48classical.lean)
-/
@[path]
private lemma bc48_burton_keane_uniqueness_via_merge_classical_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {bdry : ℕ → ℕ}
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), bc48_Tcount_classical d ω n ≤ bdry n)
  (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
  (hdens : Filter.Tendsto (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ)) Filter.atTop (nhds 0))
  (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} → 0 < μ {ω | bc47_IsClassicalTrifurcation ω 0})
  (hmergeGeom : ∀ k : ℕ∞, 2 ≤ k → k ≠ ⊤ → μ {ω | numInfiniteClusters d ω = k} = 1 → ∃ F : Finset (Sym2 (Site d)), 0 < μ (MergeWitness d F k)) :
-- imply
  (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc48_burton_keane_uniqueness_via_merge_classical μ herg hfe bdry hbound hvol hdens htrif hmergeGeom

/--
[bc48_burton_keane_bernoulli_classical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc48classical.lean)
-/
@[path]
private lemma bc48_burton_keane_bernoulli_classical_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), bc48_Tcount_classical d ω n ≤ boxSV_boundaryCard d n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | bc47_IsClassicalTrifurcation ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc48_burton_keane_bernoulli_classical hd p hp1 hp0 hbound htrif

/--
[bc48_burton_keane_bernoulli_of_classicalInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc48classical.lean)
-/
@[path]
private lemma bc48_burton_keane_bernoulli_of_classicalInjection_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hinj : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), bc48_ClassicalBoundaryArmInjection ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | bc47_IsClassicalTrifurcation ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc48_burton_keane_bernoulli_of_classicalInjection hd p hp1 hp0 hinj htrif

/--
[bc48_fakeConfig_hub_not_classicalTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc48classical.lean)
-/
@[path]
private lemma bc48_fakeConfig_hub_not_classicalTrif_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  bc47_x ∉ bc48_classicalTrifFinset bc47_fakeConfig n := by
-- proof
  apply StatMech.Walls.bc48_fakeConfig_hub_not_classicalTrif n

/--
[bc48_fakeConfig_hub_in_ambient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc48classical.lean)
-/
@[path]
private lemma bc48_fakeConfig_hub_in_ambient_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  bc47_x ∈ tfc_trifFinset bc47_fakeConfig n := by
-- proof
  apply StatMech.Walls.bc48_fakeConfig_hub_in_ambient n

/--
[bc48_fakeConfig_classical_proper_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc48classical.lean)
-/
@[path]
private lemma bc48_fakeConfig_classical_proper_subset_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  bc48_classicalTrifFinset bc47_fakeConfig n ⊂ tfc_trifFinset bc47_fakeConfig n := by
-- proof
  apply StatMech.Walls.bc48_fakeConfig_classical_proper_subset n

/--
[bc48_clawShadow_classical_fires](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc48classical.lean)
-/
@[path]
private lemma bc48_clawShadow_classical_fires_eq
  {d : ℕ} :
-- imply
  ∀ c : Fin 10, (c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) → ∃ n₁ n₂ n₃ : Fin 10, (bc46_clawLab c n₁ ≠ bc46_clawLab c n₂ ∧ bc46_clawLab c n₁ ≠ bc46_clawLab c n₃ ∧ bc46_clawLab c n₂ ≠ bc46_clawLab c n₃) ∧ (∃ z₁, bc46_clawLab c z₁ = bc46_clawLab c n₁ ∧ bc47_clawIsArm z₁ = true) ∧ (∃ z₂, bc46_clawLab c z₂ = bc46_clawLab c n₂ ∧ bc47_clawIsArm z₂ = true) ∧ (∃ z₃, bc46_clawLab c z₃ = bc46_clawLab c n₃ ∧ bc47_clawIsArm z₃ = true) := by
-- proof
  apply StatMech.Walls.bc48_clawShadow_classical_fires

/--
[bc48_classicalInjection_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc48classical.lean)
-/
@[path]
private lemma bc48_classicalInjection_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  bc48_ClassicalBoundaryArmInjection ω n := by
-- proof
  apply StatMech.Walls.bc48_classicalInjection_of_noTrif ω n hno

/--
[bc48_Tcount_classical_eq_zero_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc48classical.lean)
-/
@[path]
private lemma bc48_Tcount_classical_eq_zero_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
-- imply
  bc48_Tcount_classical d ω n = 0 := by
-- proof
  apply StatMech.Walls.bc48_Tcount_classical_eq_zero_of_noTrif ω n hno


-- created on 2026-10-23
