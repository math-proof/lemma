import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc98mcoroute
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc98_mem_precursor_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc98mcoroute.lean)
-/
@[path]
private lemma bc98_mem_precursor_iff_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a₁ a₂ a₃ x₁ x₂ x₃ : Site d} :
-- imply
  ω ∈ bc97_SingleSitePrecursor d a₁ a₂ a₃ x₁ x₂ x₃ ↔ (((hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧ (hypercubicLattice d).Adj 0 a₃) ∧ (Connected d (removeSite 0 ω) a₁ x₁ ∧ Connected d (removeSite 0 ω) a₂ x₂ ∧ Connected d (removeSite 0 ω) a₃ x₃) ∧ ((cluster d (removeSite 0 ω) x₁).Infinite ∧ (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite) ∧ (cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₂ ∧ cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₃ ∧ cluster d (removeSite 0 ω) x₂ ≠ cluster d (removeSite 0 ω) x₃)) := by
-- proof
  apply StatMech.Walls.bc98_mem_precursor_iff ω a₁ a₂ a₃ x₁ x₂ x₃

/--
[bc98_mco_iff_exists_precursor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc98mcoroute.lean)
-/
@[path]
private lemma bc98_mco_iff_exists_precursor_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  mco_ThreeClustersReachOrigin ω ↔ ∃ a₁ a₂ a₃ x₁ x₂ x₃ : Site d, ω ∈ bc97_SingleSitePrecursor d a₁ a₂ a₃ x₁ x₂ x₃ := by
-- proof
  apply StatMech.Walls.bc98_mco_iff_exists_precursor ω

/--
[bc98_measurableSet_singleSitePrecursor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc98mcoroute.lean)
-/
@[path]
private lemma bc98_measurableSet_singleSitePrecursor_eq
  {d : ℕ}
  {a₁ a₂ a₃ x₁ x₂ x₃ : Site d} :
-- imply
  MeasurableSet (bc97_SingleSitePrecursor d a₁ a₂ a₃ x₁ x₂ x₃) := by
-- proof
  apply StatMech.Walls.bc98_measurableSet_singleSitePrecursor a₁ a₂ a₃ x₁ x₂ x₃

/--
[bc98_boxRoute_of_attach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc98mcoroute.lean)
-/
@[path]
private lemma bc98_boxRoute_of_attach_eq
  {d : ℕ}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hres : tex_BoxAttachData d n)
  (hω : ω ∈ threeMeetBox d n) :
-- imply
  ∃ (a₁ a₂ a₃ x₁ x₂ x₃ : Site d) (W : Finset (Sym2 (Site d))), forceOpenFinset W ω ∈ bc97_SingleSitePrecursor d a₁ a₂ a₃ x₁ x₂ x₃ := by
-- proof
  apply StatMech.Walls.bc98_boxRoute_of_attach hres hω

/--
[bc98_precursorCover_of_attach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc98mcoroute.lean)
-/
@[path]
private lemma bc98_precursorCover_of_attach_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (hres : tex_BoxAttachData d n) :
-- imply
  threeMeetBox d n ⊆ ⋃ (a₁ : Site d) (a₂ : Site d) (a₃ : Site d) (x₁ : Site d) (x₂ : Site d) (x₃ : Site d) (W : Finset (Sym2 (Site d))), (fun ω => forceOpenFinset W ω) ⁻¹' bc97_SingleSitePrecursor d a₁ a₂ a₃ x₁ x₂ x₃ := by
-- proof
  apply StatMech.Walls.bc98_precursorCover_of_attach hres

/--
[bc98_hroute_at_of_attach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc98mcoroute.lean)
-/
@[path]
private lemma bc98_hroute_at_of_attach_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {n : ℕ}
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hres : tex_BoxAttachData d n)
  (hpos : 0 < μ (threeMeetBox d n)) :
-- imply
  ∃ a₁ a₂ a₃ x₁ x₂ x₃ : Site d, 0 < μ (bc97_SingleSitePrecursor d a₁ a₂ a₃ x₁ x₂ x₃) := by
-- proof
  apply StatMech.Walls.bc98_hroute_at_of_attach μ hfe hres hpos

/--
[bc98_hroute_of_boxAttach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc98mcoroute.lean)
-/
@[path]
private lemma bc98_hroute_of_boxAttach_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hres : ∀ n : ℕ, tex_BoxAttachData d n) :
-- imply
  0 < μ {ω | numInfiniteClusters d ω = ⊤} → ∃ a₁ a₂ a₃ x₁ x₂ x₃ : Site d, 0 < μ (bc97_SingleSitePrecursor d a₁ a₂ a₃ x₁ x₂ x₃) := by
-- proof
  apply StatMech.Walls.bc98_hroute_of_boxAttach μ hfe hres

/--
[bc98_close_a_of_boxAttach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc98mcoroute.lean)
-/
@[path]
private lemma bc98_close_a_of_boxAttach_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hres : ∀ n : ℕ, tex_BoxAttachData d n) :
-- imply
  bc95_SingleSiteRewiring μ := by
-- proof
  apply StatMech.Walls.bc98_close_a_of_boxAttach μ hfe hres

/--
[bc98_bk_from_boxAttach](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc98mcoroute.lean)
-/
@[path]
private lemma bc98_bk_from_boxAttach_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hfe : HasFiniteEnergyMerge μ)
  (hprob0 : μ {ω | bc89_GenuineTrif d ω 0} = 0)
  (hres : ∀ n : ℕ, tex_BoxAttachData d n) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc98_bk_from_boxAttach μ hfe hprob0 hres

/--
[bc98_precursor_of_contact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc98mcoroute.lean)
-/
@[path]
private lemma bc98_precursor_of_contact_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (h : tfe_TrifurcationContact ω) :
-- imply
  ∃ a₁ a₂ a₃ x₁ x₂ x₃ : Site d, ω ∈ bc97_SingleSitePrecursor d a₁ a₂ a₃ x₁ x₂ x₃ := by
-- proof
  apply StatMech.Walls.bc98_precursor_of_contact ω h

/--
[bc98_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc98mcoroute.lean)
-/
@[path]
private lemma bc98_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site 2))), mco_ThreeClustersReachOrigin ω ↔ ∃ a₁ a₂ a₃ x₁ x₂ x₃ : Site 2, ω ∈ bc97_SingleSitePrecursor 2 a₁ a₂ a₃ x₁ x₂ x₃) ∧ (∀ (a₁ a₂ a₃ x₁ x₂ x₃ : Site 2), MeasurableSet (bc97_SingleSitePrecursor 2 a₁ a₂ a₃ x₁ x₂ x₃)) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ], HasFiniteEnergyMerge μ → (∀ n : ℕ, tex_BoxAttachData 2 n) → 0 < μ {ω | numInfiniteClusters 2 ω = ⊤} → ∃ a₁ a₂ a₃ x₁ x₂ x₃ : Site 2, 0 < μ (bc97_SingleSitePrecursor 2 a₁ a₂ a₃ x₁ x₂ x₃)) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ], HasFiniteEnergyMerge μ → (∀ n : ℕ, tex_BoxAttachData 2 n) → bc95_SingleSiteRewiring μ) ∧ (∀ (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ], HasFiniteEnergyMerge μ → μ {ω | bc89_GenuineTrif 2 ω 0} = 0 → (∀ n : ℕ, tex_BoxAttachData 2 n) → μ {ω | numInfiniteClusters 2 ω = ⊤} = 0) := by
-- proof
  apply StatMech.Walls.bc98_status


-- created on 2026-10-23
