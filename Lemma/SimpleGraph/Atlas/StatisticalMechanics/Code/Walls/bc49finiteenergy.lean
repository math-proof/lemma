import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc49finiteenergy
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc49_isClassicalTrifurcation_of_neighbors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc49finiteenergy.lean)
-/
@[path]
private lemma bc49_isClassicalTrifurcation_of_neighbors_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a₁ a₂ a₃ : Site d}
-- given
  (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
  (hadj1 : (hypercubicLattice d).Adj 0 a₁)
  (hadj2 : (hypercubicLattice d).Adj 0 a₂)
  (hadj3 : (hypercubicLattice d).Adj 0 a₃)
  (hinf1 : (cluster d (removeSite 0 ω) a₁).Infinite)
  (hinf2 : (cluster d (removeSite 0 ω) a₂).Infinite)
  (hinf3 : (cluster d (removeSite 0 ω) a₃).Infinite)
  (hsep12 : ¬ Connected d (removeSite 0 ω) a₁ a₂)
  (hsep13 : ¬ Connected d (removeSite 0 ω) a₁ a₃)
  (hsep23 : ¬ Connected d (removeSite 0 ω) a₂ a₃) :
-- imply
  bc47_IsClassicalTrifurcation (forceOpenFinset {s((0:Site d), a₁), s((0:Site d), a₂), s((0:Site d), a₃)} ω) 0 := by
-- proof
  apply StatMech.Walls.bc49_isClassicalTrifurcation_of_neighbors ω a₁ a₂ a₃ hne hadj1 hadj2 hadj3 hinf1 hinf2 hinf3 hsep12 hsep13 hsep23

/--
[bc49_precursor_subset_force_classicalTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc49finiteenergy.lean)
-/
@[path]
private lemma bc49_precursor_subset_force_classicalTrif_eq
  {d : ℕ}
  {a₁ a₂ a₃ : Site d} :
-- imply
  NeighborTrifPrecursor d a₁ a₂ a₃ ⊆ (fun ω => forceOpenFinset {s((0:Site d), a₁), s((0:Site d), a₂), s((0:Site d), a₃)} ω) ⁻¹' {ω | bc47_IsClassicalTrifurcation ω 0} := by
-- proof
  apply StatMech.Walls.bc49_precursor_subset_force_classicalTrif a₁ a₂ a₃

/--
[bc49_classicalTrif_of_precursor_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc49finiteenergy.lean)
-/
@[path]
private lemma bc49_classicalTrif_of_precursor_mem_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a₁ a₂ a₃ : Site d}
-- given
  (hω : ω ∈ NeighborTrifPrecursor d a₁ a₂ a₃) :
-- imply
  bc47_IsClassicalTrifurcation (forceOpenFinset {s((0:Site d), a₁), s((0:Site d), a₂), s((0:Site d), a₃)} ω) 0 := by
-- proof
  apply StatMech.Walls.bc49_classicalTrif_of_precursor_mem ω a₁ a₂ a₃ hω

/--
[bc49_classicalTrif_pos_of_precursor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc49finiteenergy.lean)
-/
@[path]
private lemma bc49_classicalTrif_pos_of_precursor_pos_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {a₁ a₂ a₃ : Site d}
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hpos : 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃)) :
-- imply
  0 < μ {ω | bc47_IsClassicalTrifurcation ω 0} := by
-- proof
  apply StatMech.Walls.bc49_classicalTrif_pos_of_precursor_pos μ hfe a₁ a₂ a₃ hpos

/--
[bc49_classical_htrif_of_route](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc49finiteenergy.lean)
-/
@[path]
private lemma bc49_classical_htrif_of_route_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hroute : ∀ n : ℕ, 0 < μ (threeMeetBox d n) → ∃ a₁ a₂ a₃ : Site d, 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃)) :
-- imply
  0 < μ {ω | numInfiniteClusters d ω = ⊤} → 0 < μ {ω | bc47_IsClassicalTrifurcation ω 0} := by
-- proof
  apply StatMech.Walls.bc49_classical_htrif_of_route μ hfe hroute

/--
[bc49_classical_htrif_of_routingCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc49finiteenergy.lean)
-/
@[path]
private lemma bc49_classical_htrif_of_routingCover_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hrt : ∀ n : ℕ, hrHD_DisjointRouting d n) :
-- imply
  0 < μ {ω | numInfiniteClusters d ω = ⊤} → 0 < μ {ω | bc47_IsClassicalTrifurcation ω 0} := by
-- proof
  apply StatMech.Walls.bc49_classical_htrif_of_routingCover μ hfe hrt

/--
[bc49_burton_keane_bernoulli_of_route](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc49finiteenergy.lean)
-/
@[path]
private lemma bc49_burton_keane_bernoulli_of_route_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hinj : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), bc48_ClassicalBoundaryArmInjection ω n)
  (hroute : ∀ n : ℕ, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (threeMeetBox d n) → ∃ a₁ a₂ a₃ : Site d, 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (NeighborTrifPrecursor d a₁ a₂ a₃)) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc49_burton_keane_bernoulli_of_route hd p hp1 hp0 hinj hroute

/--
[bc49_burton_keane_bernoulli_of_routingCover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc49finiteenergy.lean)
-/
@[path]
private lemma bc49_burton_keane_bernoulli_of_routingCover_eq
  {d : ℕ}
-- given
  (hd : 1 ≤ d)
  (p : NNReal)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hinj : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), bc48_ClassicalBoundaryArmInjection ω n)
  (hrt : ∀ n : ℕ, hrHD_DisjointRouting d n) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 0} = 1 ∨ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω = 1} = 1) ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0 ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.Walls.bc49_burton_keane_bernoulli_of_routingCover hd p hp1 hp0 hinj hrt

/--
[bc49_precursor_forces_classicalTrif_genuinelyUsesFiniteEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc49finiteenergy.lean)
-/
@[path]
private lemma bc49_precursor_forces_classicalTrif_genuinelyUsesFiniteEnergy_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {a₁ a₂ a₃ : Site d}
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hpos : 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃)) :
-- imply
  0 < μ {ω | bc47_IsClassicalTrifurcation ω 0} := by
-- proof
  apply StatMech.Walls.bc49_precursor_forces_classicalTrif_genuinelyUsesFiniteEnergy μ hfe a₁ a₂ a₃ hpos

/--
[bc49_precursor_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc49finiteenergy.lean)
-/
@[path]
private lemma bc49_precursor_nonvacuous_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a₁ a₂ a₃ : Site d}
-- given
  (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
  (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧ (hypercubicLattice d).Adj 0 a₃)
  (hi1 : (cluster d (removeSite 0 ω) a₁).Infinite)
  (hi2 : (cluster d (removeSite 0 ω) a₂).Infinite)
  (hi3 : (cluster d (removeSite 0 ω) a₃).Infinite)
  (hd12 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₂)
  (hd13 : cluster d (removeSite 0 ω) a₁ ≠ cluster d (removeSite 0 ω) a₃)
  (hd23 : cluster d (removeSite 0 ω) a₂ ≠ cluster d (removeSite 0 ω) a₃) :
-- imply
  bc47_IsClassicalTrifurcation (forceOpenFinset {s((0:Site d), a₁), s((0:Site d), a₂), s((0:Site d), a₃)} ω) 0 := by
-- proof
  apply StatMech.Walls.bc49_precursor_nonvacuous ω a₁ a₂ a₃ hne hadj hi1 hi2 hi3 hd12 hd13 hd23


-- created on 2026-10-23
