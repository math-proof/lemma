import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bc8core
open Set SimpleGraph StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Percolation.DisjointPaths MeasureTheory StatMech StatMech.Walls


/--
[bc8_isCanonicalTrifurcation_of_arms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8core.lean)
-/
@[path]
private lemma bc8_isCanonicalTrifurcation_of_arms_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a₁ a₂ a₃ : Site d}
-- given
  (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
  (hadj : (openSubgraph d ω).Adj 0 a₁ ∧ (openSubgraph d ω).Adj 0 a₂ ∧ (openSubgraph d ω).Adj 0 a₃)
  (hinf : (cluster d (removeSite 0 ω) a₁).Infinite ∧ (cluster d (removeSite 0 ω) a₂).Infinite ∧ (cluster d (removeSite 0 ω) a₃).Infinite)
  (hcd12 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂)
  (hcd13 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃)
  (hcd23 : cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃) :
-- imply
  IsCanonicalTrifurcation d ω 0 := by
-- proof
  apply StatMech.Walls.bc8_isCanonicalTrifurcation_of_arms ω hne hadj hinf hcd12 hcd13 hcd23

/--
[bc8_arm_ne_of_cut_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8core.lean)
-/
@[path]
private lemma bc8_arm_ne_of_cut_ne_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a b : Site d}
-- given
  (h : cluster d (removeSite 0 ω) a ≠ cluster d (removeSite 0 ω) b) :
-- imply
  a ≠ b := by
-- proof
  apply StatMech.Walls.bc8_arm_ne_of_cut_ne h

/--
[bc8_isCanonicalTrifurcation_of_threeArms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8core.lean)
-/
@[path]
private lemma bc8_isCanonicalTrifurcation_of_threeArms_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a₁ a₂ a₃ : Site d}
-- given
  (hadj1 : (openSubgraph d ω).Adj 0 a₁)
  (hadj2 : (openSubgraph d ω).Adj 0 a₂)
  (hadj3 : (openSubgraph d ω).Adj 0 a₃)
  (hi1 : (cluster d (removeSite 0 ω) a₁).Infinite)
  (hi2 : (cluster d (removeSite 0 ω) a₂).Infinite)
  (hi3 : (cluster d (removeSite 0 ω) a₃).Infinite)
  (hcd12 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂)
  (hcd13 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃)
  (hcd23 : cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃) :
-- imply
  IsCanonicalTrifurcation d ω 0 := by
-- proof
  apply StatMech.Walls.bc8_isCanonicalTrifurcation_of_threeArms ω hadj1 hadj2 hadj3 hi1 hi2 hi3 hcd12 hcd13 hcd23

/--
[bc8_isCanonicalTrifurcation_of_originSplits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8core.lean)
-/
@[path]
private lemma bc8_isCanonicalTrifurcation_of_originSplits_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : ∃ a₁ a₂ a₃ : Site d, (openSubgraph d ω).Adj 0 a₁ ∧ (openSubgraph d ω).Adj 0 a₂ ∧ (openSubgraph d ω).Adj 0 a₃ ∧ (cluster d (removeSite 0 ω) a₁).Infinite ∧ (cluster d (removeSite 0 ω) a₂).Infinite ∧ (cluster d (removeSite 0 ω) a₃).Infinite ∧ cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂ ∧ cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃ ∧ cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃) :
-- imply
  IsCanonicalTrifurcation d ω 0 := by
-- proof
  apply StatMech.Walls.bc8_isCanonicalTrifurcation_of_originSplits ω h

/--
[bc8_canonicalTrif_of_originRewiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8core.lean)
-/
@[path]
private lemma bc8_canonicalTrif_of_originRewiring_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hrw : bc8_OriginRewiring d n)
  (hω : ω ∈ threeMeetBox d n) :
-- imply
  ∃ W : Finset (Sym2 (Site d)), (∀ e ∈ W, (0 : Site d) ∉ e) ∧ IsCanonicalTrifurcation d (forceOpenFinset W ω) 0 := by
-- proof
  apply StatMech.Walls.bc8_canonicalTrif_of_originRewiring n hrw ω hω

/--
[bc8_corridorWorks_of_rewiringData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8core.lean)
-/
@[path]
private lemma bc8_corridorWorks_of_rewiringData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {W : Finset (Sym2 (Site d))}
  {a₁ a₂ a₃ : Site d}
-- given
  (hadj1 : (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₁)
  (hadj2 : (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₂)
  (hadj3 : (openSubgraph d (forceOpenFinset W ω)).Adj 0 a₃)
  (hi1 : (cluster d (removeSite 0 (forceOpenFinset W ω)) a₁).Infinite)
  (hi2 : (cluster d (removeSite 0 (forceOpenFinset W ω)) a₂).Infinite)
  (hi3 : (cluster d (removeSite 0 (forceOpenFinset W ω)) a₃).Infinite)
  (hcd12 : cluster d (removeSite 0 (forceOpenFinset W ω)) a₁ ≠ cluster d (removeSite 0 (forceOpenFinset W ω)) a₂)
  (hcd13 : cluster d (removeSite 0 (forceOpenFinset W ω)) a₁ ≠ cluster d (removeSite 0 (forceOpenFinset W ω)) a₃)
  (hcd23 : cluster d (removeSite 0 (forceOpenFinset W ω)) a₂ ≠ cluster d (removeSite 0 (forceOpenFinset W ω)) a₃) :
-- imply
  ω ∈ CorridorWorks a₁ a₂ a₃ W := by
-- proof
  apply StatMech.Walls.bc8_corridorWorks_of_rewiringData ω hadj1 hadj2 hadj3 hi1 hi2 hi3 hcd12 hcd13 hcd23

/--
[bc8_threeMeetBox_subset_corridorCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8core.lean)
-/
@[path]
private lemma bc8_threeMeetBox_subset_corridorCover_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (hrw : bc8_OriginRewiring d n) :
-- imply
  threeMeetBox d n ⊆ ⋃ (a₁ : Site d) (a₂ : Site d) (a₃ : Site d) (G : Finset (Sym2 (Site d))), CorridorWorks a₁ a₂ a₃ G := by
-- proof
  apply StatMech.Walls.bc8_threeMeetBox_subset_corridorCover n hrw

/--
[bc8_hroute_of_originRewiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8core.lean)
-/
@[path]
private lemma bc8_hroute_of_originRewiring_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hrw : ∀ n : ℕ, bc8_OriginRewiring d n) :
-- imply
  ∀ n : ℕ, 0 < μ (threeMeetBox d n) → ∃ a₁ a₂ a₃ : Site d, 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃) := by
-- proof
  apply StatMech.Walls.bc8_hroute_of_originRewiring μ hfe hrw

/--
[bc8_burtonKeane_uniqueness_of_originRewiring](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8core.lean)
-/
@[path]
private lemma bc8_burtonKeane_uniqueness_of_originRewiring_eq
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
  (hrw : ∀ n : ℕ, bc8_OriginRewiring d n) :
-- imply
  (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc8_burtonKeane_uniqueness_of_originRewiring μ herg hfe bdry hbound hvol hdens hrw

/--
[bc8_threeArmsNoCrossing_isCanonical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8core.lean)
-/
@[path]
private lemma bc8_threeArmsNoCrossing_isCanonical_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hω : ω ∈ threeMeetBox d n) :
-- imply
  ∃ a₁ a₂ a₃ : Site d, (cluster d (removeSite 0 ω) a₁).Infinite ∧ (cluster d (removeSite 0 ω) a₂).Infinite ∧ (cluster d (removeSite 0 ω) a₃).Infinite ∧ cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂ ∧ cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃ ∧ cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃ ∧ bc8_NoCrossing ω a₁ a₂ ∧ bc8_NoCrossing ω a₁ a₃ ∧ bc8_NoCrossing ω a₂ a₃ := by
-- proof
  apply StatMech.Walls.bc8_threeArmsNoCrossing_isCanonical n ω hω

/--
[bc8_bridge_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc8core.lean)
-/
@[path]
private lemma bc8_bridge_nonvacuous_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : ∃ a₁ a₂ a₃ : Site d, (openSubgraph d ω).Adj 0 a₁ ∧ (openSubgraph d ω).Adj 0 a₂ ∧ (openSubgraph d ω).Adj 0 a₃ ∧ (cluster d (removeSite 0 ω) a₁).Infinite ∧ (cluster d (removeSite 0 ω) a₂).Infinite ∧ (cluster d (removeSite 0 ω) a₃).Infinite ∧ cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂ ∧ cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃ ∧ cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃) :
-- imply
  IsCanonicalTrifurcation d ω 0 := by
-- proof
  apply StatMech.Walls.bc8_bridge_nonvacuous ω h


-- created on 2026-10-23
