import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc96singlesiterewiring
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc96_genuineTrif_of_reachOrigin_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc96singlesiterewiring.lean)
-/
@[path]
private lemma bc96_genuineTrif_of_reachOrigin_full_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a₁ a₂ a₃ x₁ x₂ x₃ : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧ (hypercubicLattice d).Adj 0 a₃)
  (hconn : Connected d (removeSite 0 ω) a₁ x₁ ∧ Connected d (removeSite 0 ω) a₂ x₂ ∧ Connected d (removeSite 0 ω) a₃ x₃)
  (hinf : (cluster d (removeSite 0 ω) x₁).Infinite ∧ (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite)
  (hdist : cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₂ ∧ cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₃ ∧ cluster d (removeSite 0 ω) x₂ ≠ cluster d (removeSite 0 ω) x₃)
  (hopen : ω s(0, a₁) = true ∧ ω s(0, a₂) = true ∧ ω s(0, a₃) = true) :
-- imply
  bc89_GenuineTrif d ω 0 := by
-- proof
  apply StatMech.Walls.bc96_genuineTrif_of_reachOrigin_full ω hadj hconn hinf hdist hopen

/--
[bc96_measurableSet_openAdj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc96singlesiterewiring.lean)
-/
@[path]
private lemma bc96_measurableSet_openAdj_eq
  {d : ℕ}
  {x a : Site d} :
-- imply
  MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | (openSubgraph d ω).Adj x a} := by
-- proof
  apply StatMech.Walls.bc96_measurableSet_openAdj x a

/--
[bc96_measurableSet_removeSite_clusterInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc96singlesiterewiring.lean)
-/
@[path]
private lemma bc96_measurableSet_removeSite_clusterInfinite_eq
  {d : ℕ}
  {x a : Site d} :
-- imply
  MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | (cluster d (removeSite x ω) a).Infinite} := by
-- proof
  apply StatMech.Walls.bc96_measurableSet_removeSite_clusterInfinite x a

/--
[bc96_measurableSet_genuineTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc96singlesiterewiring.lean)
-/
@[path]
private lemma bc96_measurableSet_genuineTrif_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | bc89_GenuineTrif d ω x} := by
-- proof
  apply StatMech.Walls.bc96_measurableSet_genuineTrif x

/--
[bc96_singleSiteRewiring_of_precursor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc96singlesiterewiring.lean)
-/
@[path]
private lemma bc96_singleSiteRewiring_of_precursor_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hpre : 0 < μ {ω | numInfiniteClusters d ω = ⊤} → ∃ (G : Finset (Sym2 (Site d))) (A : Set (ConfigSpace (Sym2 (Site d)))), 0 < μ A ∧ A ⊆ (fun ω => forceOpenFinset G ω) ⁻¹' {ω | bc89_GenuineTrif d ω 0}) :
-- imply
  bc95_SingleSiteRewiring μ := by
-- proof
  apply StatMech.Walls.bc96_singleSiteRewiring_of_precursor μ hfe hpre

/--
[bc96_bk_from_precursor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc96singlesiterewiring.lean)
-/
@[path]
private lemma bc96_bk_from_precursor_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hprob0 : μ {ω | bc89_GenuineTrif d ω 0} = 0)
  (hpre : 0 < μ {ω | numInfiniteClusters d ω = ⊤} → ∃ (G : Finset (Sym2 (Site d))) (A : Set (ConfigSpace (Sym2 (Site d)))), 0 < μ A ∧ A ⊆ (fun ω => forceOpenFinset G ω) ⁻¹' {ω | bc89_GenuineTrif d ω 0}) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc96_bk_from_precursor μ hfe hprob0 hpre

/--
[bc96_arm_reaches_boundary_perConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc96singlesiterewiring.lean)
-/
@[path]
private lemma bc96_arm_reaches_boundary_perConfig_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x a : Site d}
  {n : ℕ}
-- given
  (hinf : (cluster d (removeSite x ω) a).Infinite) :
-- imply
  ∃ z, z ∉ box d n ∧ Connected d (removeSite x ω) a z := by
-- proof
  apply StatMech.Walls.bc96_arm_reaches_boundary_perConfig ω x a hinf n

/--
[bc96_harmbox_free_of_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc96singlesiterewiring.lean)
-/
@[path]
private lemma bc96_harmbox_free_of_interior_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x : Site d}
  {a : Site d}
-- given
  (hn : 1 ≤ n)
  (hxint : x ∈ box d (n - 1))
  (hadj : (openSubgraph d ω).Adj x a) :
-- imply
  a ∈ box d n := by
-- proof
  apply StatMech.Walls.bc96_harmbox_free_of_interior ω hn hxint hadj

/--
[bc96_harmbox_not_perConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc96singlesiterewiring.lean)
-/
@[path]
private lemma bc96_harmbox_not_perConfig_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
  {x a : Site d}
-- given
  (hxbox : x ∈ box d n)
  (htri : IsTrifurcation d ω x)
  (hadj : (openSubgraph d ω).Adj x a)
  (hinf : (cluster d (removeSite x ω) a).Infinite)
  (hout : a ∉ box d n) :
-- imply
  ¬ (∀ y, y ∈ box d n → IsTrifurcation d ω y → ∀ b, (openSubgraph d ω).Adj y b → (cluster d (removeSite y ω) b).Infinite → b ∈ box d n) := by
-- proof
  apply StatMech.Walls.bc96_harmbox_not_perConfig ω n hxbox htri hadj hinf hout

/--
[bc96_genuineTrif_of_mco](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc96singlesiterewiring.lean)
-/
@[path]
private lemma bc96_genuineTrif_of_mco_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : mco_ThreeClustersReachOrigin ω)
  (hopen : ∀ a : Site d, (hypercubicLattice d).Adj 0 a → (∃ x, Connected d (removeSite 0 ω) a x ∧ (cluster d (removeSite 0 ω) x).Infinite) → ω s(0, a) = true) :
-- imply
  bc89_GenuineTrif d ω 0 := by
-- proof
  apply StatMech.Walls.bc96_genuineTrif_of_mco ω h hopen

/--
[bc96_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc96singlesiterewiring.lean)
-/
@[path]
private lemma bc96_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site 2))) {a₁ a₂ a₃ x₁ x₂ x₃ : Site 2}, ((hypercubicLattice 2).Adj 0 a₁ ∧ (hypercubicLattice 2).Adj 0 a₂ ∧ (hypercubicLattice 2).Adj 0 a₃) → (Connected 2 (removeSite 0 ω) a₁ x₁ ∧ Connected 2 (removeSite 0 ω) a₂ x₂ ∧ Connected 2 (removeSite 0 ω) a₃ x₃) → ((cluster 2 (removeSite 0 ω) x₁).Infinite ∧ (cluster 2 (removeSite 0 ω) x₂).Infinite ∧ (cluster 2 (removeSite 0 ω) x₃).Infinite) → (cluster 2 (removeSite 0 ω) x₁ ≠ cluster 2 (removeSite 0 ω) x₂ ∧ cluster 2 (removeSite 0 ω) x₁ ≠ cluster 2 (removeSite 0 ω) x₃ ∧ cluster 2 (removeSite 0 ω) x₂ ≠ cluster 2 (removeSite 0 ω) x₃) → (ω s(0, a₁) = true ∧ ω s(0, a₂) = true ∧ ω s(0, a₃) = true) → bc89_GenuineTrif 2 ω 0) ∧ (MeasurableSet {ω : ConfigSpace (Sym2 (Site 2)) | bc89_GenuineTrif 2 ω 0}) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ], HasFiniteEnergyMerge μ → (0 < μ {ω | numInfiniteClusters 2 ω = ⊤} → ∃ (G : Finset (Sym2 (Site 2))) (A : Set (ConfigSpace (Sym2 (Site 2)))), 0 < μ A ∧ A ⊆ (fun ω => forceOpenFinset G ω) ⁻¹' {ω | bc89_GenuineTrif 2 ω 0}) → bc95_SingleSiteRewiring μ) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (x a : Site 2), (cluster 2 (removeSite x ω) a).Infinite → ∀ n : ℕ, ∃ z, z ∉ box 2 n ∧ Connected 2 (removeSite x ω) a z) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ], HasFiniteEnergyMerge μ → μ {ω | bc89_GenuineTrif 2 ω 0} = 0 → (0 < μ {ω | numInfiniteClusters 2 ω = ⊤} → ∃ (G : Finset (Sym2 (Site 2))) (A : Set (ConfigSpace (Sym2 (Site 2)))), 0 < μ A ∧ A ⊆ (fun ω => forceOpenFinset G ω) ⁻¹' {ω | bc89_GenuineTrif 2 ω 0}) → μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) := by
-- proof
  apply StatMech.Walls.bc96_status


-- created on 2026-10-23
