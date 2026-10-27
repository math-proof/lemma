import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Percolation


/--
[tfc_boundary_cross_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationCount.lean)
-/
@[path]
private lemma tfc_boundary_cross_vertex_eq
  {d : ℕ}
  {n : ℕ}
  {z z' : Site d}
-- given
  (hn : 1 ≤ n)
  (hz : z ∈ box d n)
  (hz' : z' ∉ box d n)
  (hadj : (hypercubicLattice d).Adj z z') :
-- imply
  z ∈ vertexBoundary d n := by
-- proof
  apply StatMech.Percolation.tfc_boundary_cross_vertex n hn z z' hz hz' hadj

/--
[tfc_walk_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationCount.lean)
-/
@[path]
private lemma tfc_walk_crossing_eq
  {d : ℕ}
  {G : SimpleGraph V}
  [DecidablePred p]
-- given
  (p : V → Prop) :
-- imply
  ∀ {x y : V} (w : G.Walk x y), p x → ¬ p y → ∃ a b, G.Adj a b ∧ p a ∧ ¬ p b ∧ G.Reachable x a := by
-- proof
  apply StatMech.Percolation.tfc_walk_crossing G p

/--
[tfc_trif_cluster_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationCount.lean)
-/
@[path]
private lemma tfc_trif_cluster_infinite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (htri : IsTrifurcation d ω x) :
-- imply
  (cluster d ω x).Infinite := by
-- proof
  apply StatMech.Percolation.tfc_trif_cluster_infinite ω x htri

/--
[tfc_trif_reaches_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationCount.lean)
-/
@[path]
private lemma tfc_trif_reaches_boundary_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Site d}
-- given
  (hn : 1 ≤ n)
  (hxbox : x ∈ box d n)
  (htri : IsTrifurcation d ω x) :
-- imply
  ∃ z ∈ vertexBoundary d n, Connected d ω x z := by
-- proof
  apply StatMech.Percolation.tfc_trif_reaches_boundary ω n hn x hxbox htri

/--
[tfc_trifFinset_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationCount.lean)
-/
@[path]
private lemma tfc_trifFinset_card_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  (tfc_trifFinset ω n).card = Tcount d ω n := by
-- proof
  apply StatMech.Percolation.tfc_trifFinset_card ω n

/--
[tfc_boundaryFinset_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationCount.lean)
-/
@[path]
private lemma tfc_boundaryFinset_card_eq
  {d : ℕ}
  {d n : ℕ} :
-- imply
  (tfc_boundaryFinset d n).card = boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.tfc_boundaryFinset_card d n

/--
[tfc_mem_trifFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationCount.lean)
-/
@[path]
private lemma tfc_mem_trifFinset_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Site d} :
-- imply
  x ∈ tfc_trifFinset ω n ↔ x ∈ box d n ∧ IsTrifurcation d ω x := by
-- proof
  apply StatMech.Percolation.tfc_mem_trifFinset

/--
[tfc_mem_boundaryFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationCount.lean)
-/
@[path]
private lemma tfc_mem_boundaryFinset_eq
  {d : ℕ}
  {d n : ℕ}
  {x : Site d} :
-- imply
  x ∈ tfc_boundaryFinset d n ↔ x ∈ vertexBoundary d n := by
-- proof
  apply StatMech.Percolation.tfc_mem_boundaryFinset

/--
[tfc_boundaryCard_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationCount.lean)
-/
@[path]
private lemma tfc_boundaryCard_zero_eq
  {d : ℕ}
  {d : ℕ} :
-- imply
  boxSV_boundaryCard d 0 = 0 := by
-- proof
  apply StatMech.Percolation.tfc_boundaryCard_zero d

/--
[tfc_Tcount_le_of_injOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationCount.lean)
-/
@[path]
private lemma tfc_Tcount_le_of_injOn_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {φ : Site d → Site d}
-- given
  (hmaps : ∀ x, x ∈ box d n → IsTrifurcation d ω x → φ x ∈ vertexBoundary d n)
  (hinj : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → φ x = φ y → x = y) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.tfc_Tcount_le_of_injOn ω n φ hmaps hinj

/--
[tfc_Tcount_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationCount.lean)
-/
@[path]
private lemma tfc_Tcount_le_card_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {φ : Site d → Site d}
-- given
  (hmaps : Set.MapsTo φ (tfc_trifFinset ω n) (tfc_boundaryFinset d n))
  (hinj : Set.InjOn φ (tfc_trifFinset ω n)) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.tfc_Tcount_le_card ω n φ hmaps hinj

/--
[tfc_Tcount_le_boundary_of_residue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationCount.lean)
-/
@[path]
private lemma tfc_Tcount_le_boundary_of_residue_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : tfc_BoundaryArmInjection ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.tfc_Tcount_le_boundary_of_residue ω n h

/--
[tfc_Tcount_le_boundary_of_injection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationCount.lean)
-/
@[path]
private lemma tfc_Tcount_le_boundary_of_injection_eq
  {d : ℕ}
-- given
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), tfc_BoundaryArmInjection ω n) :
-- imply
  ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.tfc_Tcount_le_boundary_of_injection hres

/--
[tfc_boundaryArmInjection_of_distinctArmEnds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationCount.lean)
-/
@[path]
private lemma tfc_boundaryArmInjection_of_distinctArmEnds_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : tfc_DistinctArmEnds ω n) :
-- imply
  tfc_BoundaryArmInjection ω n := by
-- proof
  apply StatMech.Percolation.tfc_boundaryArmInjection_of_distinctArmEnds ω n h

/--
[tfc_Tcount_le_boundary_of_distinctArmEnds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationCount.lean)
-/
@[path]
private lemma tfc_Tcount_le_boundary_of_distinctArmEnds_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : tfc_DistinctArmEnds ω n) :
-- imply
  Tcount d ω n ≤ boxSV_boundaryCard d n := by
-- proof
  apply StatMech.Percolation.tfc_Tcount_le_boundary_of_distinctArmEnds ω n h

/--
[tfc_armEnds_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationCount.lean)
-/
@[path]
private lemma tfc_armEnds_nonempty_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Site d}
-- given
  (hn : 1 ≤ n)
  (hxbox : x ∈ box d n)
  (htri : IsTrifurcation d ω x) :
-- imply
  (tfc_armEnds ω n x).Nonempty := by
-- proof
  apply StatMech.Percolation.tfc_armEnds_nonempty ω n hn x hxbox htri

/--
[tfc_distinctArmEnds_iff_injSelector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationCount.lean)
-/
@[path]
private lemma tfc_distinctArmEnds_iff_injSelector_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  tfc_DistinctArmEnds ω n ↔ ∃ φ : Site d → Site d, (∀ x, x ∈ box d n → IsTrifurcation d ω x → φ x ∈ tfc_armEnds ω n x) ∧ (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y → φ x = φ y → x = y) := by
-- proof
  apply StatMech.Percolation.tfc_distinctArmEnds_iff_injSelector ω n

/--
[tfc_distinctArmEnds_of_subsingleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationCount.lean)
-/
@[path]
private lemma tfc_distinctArmEnds_of_subsingleton_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (hn : 1 ≤ n)
  (hsub : ∀ x y, x ∈ box d n → IsTrifurcation d ω x → y ∈ box d n → IsTrifurcation d ω y → x = y) :
-- imply
  tfc_DistinctArmEnds ω n := by
-- proof
  apply StatMech.Percolation.tfc_distinctArmEnds_of_subsingleton ω n hn hsub

/--
[tfc_residue_zero_iff_no_origin_trif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationCount.lean)
-/
@[path]
private lemma tfc_residue_zero_iff_no_origin_trif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  tfc_BoundaryArmInjection ω 0 ↔ ¬ IsTrifurcation d ω 0 := by
-- proof
  apply StatMech.Percolation.tfc_residue_zero_iff_no_origin_trif ω

/--
[tfc_Tcount_zero_le_boundary_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationCount.lean)
-/
@[path]
private lemma tfc_Tcount_zero_le_boundary_iff_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  Tcount d ω 0 ≤ boxSV_boundaryCard d 0 ↔ ¬ IsTrifurcation d ω 0 := by
-- proof
  apply StatMech.Percolation.tfc_Tcount_zero_le_boundary_iff ω

/--
[tfc_trifurcation_prob_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationCount.lean)
-/
@[path]
private lemma tfc_trifurcation_prob_eq_zero_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {bdry : ℕ → ℕ}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → Tcount d ω n ≤ bdry n)
  (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
  (hdens : Tendsto (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ)) atTop (𝓝 0)) :
-- imply
  μ {ω | IsTrifurcation d ω 0} = 0 := by
-- proof
  apply StatMech.Percolation.tfc_trifurcation_prob_eq_zero μ hinv bdry hbound hvol hdens

/--
[tfc_numInfiniteClusters_ae_const_ne_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationCount.lean)
-/
@[path]
private lemma tfc_numInfiniteClusters_ae_const_ne_top_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {bdry : ℕ → ℕ}
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → Tcount d ω n ≤ bdry n)
  (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
  (hdens : Tendsto (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ)) atTop (𝓝 0))
  (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} → 0 < μ {ω | IsTrifurcation d ω 0}) :
-- imply
  ∃ k : ℕ∞, k ≠ ⊤ ∧ μ {ω | numInfiniteClusters d ω = k} = 1 := by
-- proof
  apply StatMech.Percolation.tfc_numInfiniteClusters_ae_const_ne_top μ herg bdry hbound hvol hdens htrif

/--
[tfc_burton_keane_uniqueness_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationCount.lean)
-/
@[path]
private lemma tfc_burton_keane_uniqueness_full_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {bdry : ℕ → ℕ}
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hfe : HasFiniteEnergyMerge μ)
  (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → Tcount d ω n ≤ bdry n)
  (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
  (hdens : Tendsto (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ)) atTop (𝓝 0))
  (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} → 0 < μ {ω | IsTrifurcation d ω 0}) :
-- imply
  (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.tfc_burton_keane_uniqueness_full μ herg hfe bdry hbound hvol hdens htrif

/--
[tfc_burton_keane_bernoulli](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationCount.lean)
-/
@[path]
private lemma tfc_burton_keane_bernoulli_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → tfc_DistinctArmEnds ω n)
  (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = ⊤} → 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | IsTrifurcation d ω 0}) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Percolation.tfc_burton_keane_bernoulli hd p hp1 hp0 hres htrif


-- created on 2026-10-23
