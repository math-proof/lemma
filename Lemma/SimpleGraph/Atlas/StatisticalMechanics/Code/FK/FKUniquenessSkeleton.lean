import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessSkeleton.Part3
open MeasureTheory Set Filter Topology StatMech StatMech.FK


/--
[fuc_real_preimage_eq_indicator_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessSkeleton.lean)
-/
@[path]
private lemma fuc_real_preimage_eq_indicator_sum_eq
  [Fintype β]
  [MeasurableSpace α]
  [MeasurableSpace β]
  [MeasurableSingletonClass β]
  {μ : Measure α}
  [IsFiniteMeasure μ]
  {f : α → β}
  {A : Set β}
-- given
  (hf : Measurable f) :
-- imply
  μ.real (f ⁻¹' A) = ∑ ω : β, A.indicator (fun _ => (1 : ℝ)) ω * μ.real (f ⁻¹' {ω}) := by
-- proof
  apply StatMech.FK.fuc_real_preimage_eq_indicator_sum μ f hf A

/--
[fuc_sum_real_preimage_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessSkeleton.lean)
-/
@[path]
private lemma fuc_sum_real_preimage_eq_one_eq
  [Fintype β]
  [MeasurableSpace α]
  [MeasurableSpace β]
  [MeasurableSingletonClass β]
  {μ : Measure α}
  [IsProbabilityMeasure μ]
  {f : α → β}
-- given
  (hf : Measurable f) :
-- imply
  ∑ ω : β, μ.real (f ⁻¹' {ω}) = 1 := by
-- proof
  apply StatMech.FK.fuc_sum_real_preimage_eq_one μ f hf

/--
[fuc_measOfMass_real_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessSkeleton.lean)
-/
@[path]
private lemma fuc_measOfMass_real_singleton_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {x : ConfigSpace E}
-- given
  (hμ : 0 ≤ μ) :
-- imply
  (measOfMass μ).real {x} = μ x := by
-- proof
  apply StatMech.FK.fuc_measOfMass_real_singleton hμ x

/--
[fuc_isMonotoneCouplingFun_of_monotoneCoupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessSkeleton.lean)
-/
@[path]
private lemma fuc_isMonotoneCouplingFun_of_monotoneCoupling_eq
  [Fintype E]
  [DecidableEq E]
  {μ ν : ConfigSpace E → ℝ}
  {κ : Measure (ConfigSpace E × ConfigSpace E)}
  [IsFiniteMeasure κ]
-- given
  (hμ : 0 ≤ μ)
  (hν : 0 ≤ ν)
  (hcoup : MonotoneCoupling (measOfMass μ) (measOfMass ν) κ) :
-- imply
  IsMonotoneCouplingFun (fun z => κ.real {z}) μ ν := by
-- proof
  apply StatMech.FK.fuc_isMonotoneCouplingFun_of_monotoneCoupling hμ hν hcoup

/--
[fuc_isMonotoneCouplingFun_of_dominated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessSkeleton.lean)
-/
@[path]
private lemma fuc_isMonotoneCouplingFun_of_dominated_eq
  [Fintype E]
  [DecidableEq E]
  {μ ν : ConfigSpace E → ℝ}
-- given
  (hμ : 0 ≤ μ)
  (hν : 0 ≤ ν)
  (hnμ : ∑ ω, μ ω = 1)
  (hnν : ∑ ω, ν ω = 1)
  (hdom : measOfMass μ ≼ measOfMass ν) :
-- imply
  ∃ P : ConfigSpace E × ConfigSpace E → ℝ, IsMonotoneCouplingFun P μ ν := by
-- proof
  apply StatMech.FK.fuc_isMonotoneCouplingFun_of_dominated hμ hν hnμ hnν hdom

/--
[fuc_freeMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessSkeleton.lean)
-/
@[path]
private lemma fuc_freeMass_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {d N : ℕ}
  {t : ℝ} :
-- imply
  0 ≤ fuc_freeMass d N t := by
-- proof
  apply StatMech.FK.fuc_freeMass_nonneg d N t

/--
[fuc_wiredMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessSkeleton.lean)
-/
@[path]
private lemma fuc_wiredMass_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {d N : ℕ}
  {t : ℝ} :
-- imply
  0 ≤ fuc_wiredMass d N t := by
-- proof
  apply StatMech.FK.fuc_wiredMass_nonneg d N t

/--
[fuc_freeMass_sum_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessSkeleton.lean)
-/
@[path]
private lemma fuc_freeMass_sum_one_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {d N : ℕ}
  {t : ℝ} :
-- imply
  ∑ ω, fuc_freeMass d N t ω = 1 := by
-- proof
  apply StatMech.FK.fuc_freeMass_sum_one d N t

/--
[fuc_wiredMass_sum_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessSkeleton.lean)
-/
@[path]
private lemma fuc_wiredMass_sum_one_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {d N : ℕ}
  {t : ℝ} :
-- imply
  ∑ ω, fuc_wiredMass d N t ω = 1 := by
-- proof
  apply StatMech.FK.fuc_wiredMass_sum_one d N t

/--
[fuc_eventMassProb_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessSkeleton.lean)
-/
@[path]
private lemma fuc_eventMassProb_free_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {d N : ℕ}
  {t : ℝ}
  {A : Set (ConfigSpace (Sym2 (boxVerts d N)))} :
-- imply
  eventMassProb (fuc_freeMass d N t) A = (freeInfiniteVolume d (fsc_logistic_pos t) (fsc_logistic_lt_one t) (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' A) := by
-- proof
  apply StatMech.FK.fuc_eventMassProb_free d N t A

/--
[fuc_eventMassProb_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessSkeleton.lean)
-/
@[path]
private lemma fuc_eventMassProb_wired_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {d N : ℕ}
  {t : ℝ}
  {A : Set (ConfigSpace (Sym2 (boxVerts d N)))} :
-- imply
  eventMassProb (fuc_wiredMass d N t) A = (wiredInfiniteVolume d (fsc_logistic_pos t) (fsc_logistic_lt_one t) (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' A) := by
-- proof
  apply StatMech.FK.fuc_eventMassProb_wired d N t A

/--
[fuc_edgeMargProb_eq_eventMassProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessSkeleton.lean)
-/
@[path]
private lemma fuc_edgeMargProb_eq_eventMassProb_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {μ : ConfigSpace (Sym2 (boxVerts d N)) → ℝ}
  {e' : Sym2 (boxVerts d N)} :
-- imply
  edgeMargProb μ e' = eventMassProb μ (boxEdgeOpenEvent d N e') := by
-- proof
  apply StatMech.FK.fuc_edgeMargProb_eq_eventMassProb μ e'

/--
[fuc_edgeMargProb_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessSkeleton.lean)
-/
@[path]
private lemma fuc_edgeMargProb_free_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {d N : ℕ}
  {t : ℝ}
  {e' : Sym2 (boxVerts d N)} :
-- imply
  edgeMargProb (fuc_freeMass d N t) e' = freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) := by
-- proof
  apply StatMech.FK.fuc_edgeMargProb_free d N t e'

/--
[fuc_edgeMargProb_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessSkeleton.lean)
-/
@[path]
private lemma fuc_edgeMargProb_wired_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {d N : ℕ}
  {t : ℝ}
  {e' : Sym2 (boxVerts d N)} :
-- imply
  edgeMargProb (fuc_wiredMass d N t) e' = wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) := by
-- proof
  apply StatMech.FK.fuc_edgeMargProb_wired d N t e'

/--
[fuc_freeIV_le_wiredIV](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessSkeleton.lean)
-/
@[path]
private lemma fuc_freeIV_le_wiredIV_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {d N : ℕ}
  {p : ℝ}
  {S : Set (ConfigSpace (Sym2 (boxVerts d N)))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hS : IsIncreasing S) :
-- imply
  (freeInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' S) := by
-- proof
  apply StatMech.FK.fuc_freeIV_le_wiredIV d N hp hp1 hS

/--
[fuc_dominated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessSkeleton.lean)
-/
@[path]
private lemma fuc_dominated_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {d N : ℕ}
  {t : ℝ} :
-- imply
  measOfMass (fuc_freeMass d N t) ≼ measOfMass (fuc_wiredMass d N t) := by
-- proof
  apply StatMech.FK.fuc_dominated d N t

/--
[fuc_hcoup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessSkeleton.lean)
-/
@[path]
private lemma fuc_hcoup_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {d N : ℕ} :
-- imply
  ∀ t : ℝ, ∃ P : ConfigSpace (Sym2 (boxVerts d N)) × ConfigSpace (Sym2 (boxVerts d N)) → ℝ, IsMonotoneCouplingFun P (fuc_freeMass d N t) (fuc_wiredMass d N t) := by
-- proof
  apply StatMech.FK.fuc_hcoup d N

/--
[fuc_hmono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessSkeleton.lean)
-/
@[path]
private lemma fuc_hmono_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)} :
-- imply
  Monotone (fun t => edgeMargProb (fuc_wiredMass d N t) eb) := by
-- proof
  apply StatMech.FK.fuc_hmono d N eb

/--
[fuc_fk_uniqueness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessSkeleton.lean)
-/
@[path]
private lemma fuc_fk_uniqueness_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)}
-- given
  (hdata : fuc_HomogeneousFreeEnergyData d N) :
-- imply
  {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧ eventMassProb (fuc_freeMass d N t) A ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
-- proof
  apply StatMech.FK.fuc_fk_uniqueness d N eb hdata

/--
[fuc_homogeneousData_imp_fsc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniquenessSkeleton.lean)
-/
@[path]
private lemma fuc_homogeneousData_imp_fsc_eq
  [Fintype E]
  [DecidableEq E]
  {d : ℕ}
  {d N : ℕ}
  {eb : Sym2 (boxVerts d N)}
-- given
  (hdata : fuc_HomogeneousFreeEnergyData d N) :
-- imply
  fsc_FreeEnergyData d N eb := by
-- proof
  apply StatMech.FK.fuc_homogeneousData_imp_fsc d N eb hdata


-- created on 2026-10-23
