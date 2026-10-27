import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentTraceCoarseUniqueness
open MeasureTheory Set StatMech StatMech.FrontierB


/--
[removeSites_forceOpenFinset_eq_of_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCoarseUniqueness.lean)
-/
@[path]
private lemma removeSites_forceOpenFinset_eq_of_incident_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {F : Finset (Sym2 (Site d))}
  {ω : ConfigSpace (Sym2 (Site d))}
-- given
  (hF : ∀ e ∈ F, ∃ t ∈ T, t ∈ e) :
-- imply
  removeSites T (forceOpenFinset F ω) = removeSites T ω := by
-- proof
  apply StatMech.FrontierB.removeSites_forceOpenFinset_eq_of_incident T F hF ω

/--
[boxEdges_incident_to_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCoarseUniqueness.lean)
-/
@[path]
private lemma boxEdges_incident_to_box_eq
  {d : ℕ}
  {d n : ℕ} :
-- imply
  ∀ e ∈ boxEdges d n, ∃ t ∈ boxFinsetBK d n, t ∈ e := by
-- proof
  apply StatMech.FrontierB.boxEdges_incident_to_box d n

/--
[removeBox_forceOpen_boxEdges_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCoarseUniqueness.lean)
-/
@[path]
private lemma removeBox_forceOpen_boxEdges_eq_eq
  {d : ℕ}
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  removeSites (bc61_boxAround d n 0) (forceOpenFinset (boxEdges d n) ω) = removeSites (bc61_boxAround d n 0) ω := by
-- proof
  apply StatMech.FrontierB.removeBox_forceOpen_boxEdges_eq d n ω

/--
[forceOpen_boxEdges_bgfdIndexAllOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCoarseUniqueness.lean)
-/
@[path]
private lemma forceOpen_boxEdges_bgfdIndexAllOpen_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  BgfdIndexAllOpen (forceOpenFinset (boxEdges d n) ω) n 0 := by
-- proof
  apply StatMech.FrontierB.forceOpen_boxEdges_bgfdIndexAllOpen ω n

/--
[coarseTrif_forceOpen_boxEdges_of_coarse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCoarseUniqueness.lean)
-/
@[path]
private lemma coarseTrif_forceOpen_boxEdges_of_coarse_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : bc61_IsCoarseTrifurcation ω n 0) :
-- imply
  bc61_IsCoarseTrifurcation (forceOpenFinset (boxEdges d n) ω) n 0 := by
-- proof
  apply StatMech.FrontierB.coarseTrif_forceOpen_boxEdges_of_coarse ω n h

/--
[forceOpen_boxEdges_faithfulAllOpenTrif_of_threeMeetBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCoarseUniqueness.lean)
-/
@[path]
private lemma forceOpen_boxEdges_faithfulAllOpenTrif_of_threeMeetBox_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ}
-- given
  (h : ω ∈ threeMeetBox d n) :
-- imply
  BgfdFaithfulAllOpenTrifAt (forceOpenFinset (boxEdges d n) ω) n 0 := by
-- proof
  apply StatMech.FrontierB.forceOpen_boxEdges_faithfulAllOpenTrif_of_threeMeetBox ω n h

/--
[threeMeetBox_subset_force_faithfulAllOpenTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCoarseUniqueness.lean)
-/
@[path]
private lemma threeMeetBox_subset_force_faithfulAllOpenTrif_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  threeMeetBox d n ⊆ (fun ω => forceOpenFinset (boxEdges d n) ω) ⁻¹' {ω | BgfdFaithfulAllOpenTrifAt ω n 0} := by
-- proof
  apply StatMech.FrontierB.threeMeetBox_subset_force_faithfulAllOpenTrif n

/--
[faithfulAllOpenTrif_pos_of_threeMeetBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCoarseUniqueness.lean)
-/
@[path]
private lemma faithfulAllOpenTrif_pos_of_threeMeetBox_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  {n : ℕ}
-- given
  (hfe : HasLatticeFiniteEnergyMerge μ)
  (hpos : 0 < μ (threeMeetBox d n)) :
-- imply
  0 < μ {ω | BgfdFaithfulAllOpenTrifAt ω n 0} := by
-- proof
  apply StatMech.FrontierB.faithfulAllOpenTrif_pos_of_threeMeetBox μ hfe n hpos

/--
[infiniteClusters_top_null_of_latticeFiniteEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCoarseUniqueness.lean)
-/
@[path]
private lemma infiniteClusters_top_null_of_latticeFiniteEnergy_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hd : 1 ≤ d)
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hfe : HasLatticeFiniteEnergyMerge μ) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.FrontierB.infiniteClusters_top_null_of_latticeFiniteEnergy μ hd hinv hfe

/--
[latticeFiniteEnergy_coarse_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCoarseUniqueness.lean)
-/
@[path]
private lemma latticeFiniteEnergy_coarse_uniqueness_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hd : 1 ≤ d)
  (herg : IsErgodic (G := Multiplicative (Site d)) μ)
  (hfe : HasLatticeFiniteEnergyMerge μ) :
-- imply
  (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.FrontierB.latticeFiniteEnergy_coarse_uniqueness μ hd herg hfe

/--
[freeFreeSuperposedTraceLaw_coarse_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCoarseUniqueness.lean)
-/
@[path]
private lemma freeFreeSuperposedTraceLaw_coarse_uniqueness_eq
  {d : ℕ}
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 < beta)
  (hd : 1 ≤ d)
  (herg : IsErgodic (G := Multiplicative (Site d)) (independentSuperposedTraceLaw (infiniteFreeCurrentMeasure d beta hbeta.le) (infiniteFreeCurrentMeasure d beta hbeta.le) : Measure (ConfigSpace (Sym2 (Site d))))) :
-- imply
  let μ := (independentSuperposedTraceLaw (infiniteFreeCurrentMeasure d beta hbeta.le) (infiniteFreeCurrentMeasure d beta hbeta.le) : Measure (ConfigSpace (Sym2 (Site d)))) (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.FrontierB.freeFreeSuperposedTraceLaw_coarse_uniqueness d beta hbeta hd herg

/--
[freePlusSuperposedTraceLaw_coarse_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCoarseUniqueness.lean)
-/
@[path]
private lemma freePlusSuperposedTraceLaw_coarse_uniqueness_eq
  {d : ℕ}
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 < beta)
  (hd : 1 ≤ d)
  (herg : IsErgodic (G := Multiplicative (Site d)) (independentSuperposedTraceLaw (infiniteFreeCurrentMeasure d beta hbeta.le) (infinitePlusCurrentMeasure d beta hbeta.le) : Measure (ConfigSpace (Sym2 (Site d))))) :
-- imply
  let μ := (independentSuperposedTraceLaw (infiniteFreeCurrentMeasure d beta hbeta.le) (infinitePlusCurrentMeasure d beta hbeta.le) : Measure (ConfigSpace (Sym2 (Site d)))) (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.FrontierB.freePlusSuperposedTraceLaw_coarse_uniqueness d beta hbeta hd herg

/--
[plusPlusSuperposedTraceLaw_coarse_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/CurrentTraceCoarseUniqueness.lean)
-/
@[path]
private lemma plusPlusSuperposedTraceLaw_coarse_uniqueness_eq
  {d : ℕ}
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : 0 < beta)
  (hd : 1 ≤ d)
  (herg : IsErgodic (G := Multiplicative (Site d)) (independentSuperposedTraceLaw (infinitePlusCurrentMeasure d beta hbeta.le) (infinitePlusCurrentMeasure d beta hbeta.le) : Measure (ConfigSpace (Sym2 (Site d))))) :
-- imply
  let μ := (independentSuperposedTraceLaw (infinitePlusCurrentMeasure d beta hbeta.le) (infinitePlusCurrentMeasure d beta hbeta.le) : Measure (ConfigSpace (Sym2 (Site d)))) (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1) ∧ μ (atLeastTwoInfinite d) = 0 ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
-- proof
  apply StatMech.FrontierB.plusPlusSuperposedTraceLaw_coarse_uniqueness d beta hbeta hd herg


-- created on 2026-10-23
