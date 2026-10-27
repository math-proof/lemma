import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.FKMixingUpperClose.Part5
open MeasureTheory Filter Topology Set StatMech.ConfigSpace StatMech.Lattice StatMech StatMech.FK


/--
[fmu_moInd_eq_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean)
-/
@[path]
private lemma fmu_moInd_eq_indicator_eq
  [Group G]
  [MulAction G E]
  {T : Finset E}
  {ω : ConfigSpace E} :
-- imply
  fmu_moInd T ω = (fmu_multiOpen T).indicator (fun _ => (1:ℝ)) ω := by
-- proof
  apply StatMech.FK.fmu_moInd_eq_indicator T ω

/--
[fmu_multiOpen_measurable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean)
-/
@[path]
private lemma fmu_multiOpen_measurable_eq
  [Group G]
  [MulAction G E]
  [Countable E]
  {T : Finset E} :
-- imply
  MeasurableSet (fmu_multiOpen T) := by
-- proof
  apply StatMech.FK.fmu_multiOpen_measurable T

/--
[fmu_multiOpen_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean)
-/
@[path]
private lemma fmu_multiOpen_isIncreasing_eq
  [Group G]
  [MulAction G E]
  {T : Finset E} :
-- imply
  IsIncreasing (fmu_multiOpen T) := by
-- proof
  apply StatMech.FK.fmu_multiOpen_isIncreasing T

/--
[fmu_shift_multiOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean)
-/
@[path]
private lemma fmu_shift_multiOpen_eq
  [Group G]
  [MulAction G E]
  [DecidableEq E]
  {g : G}
  {T : Finset E} :
-- imply
  (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' (fmu_multiOpen T) = fmu_multiOpen (T.image (fun e => g⁻¹ • e)) := by
-- proof
  apply StatMech.FK.fmu_shift_multiOpen g T

/--
[fmu_indicator_mul_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean)
-/
@[path]
private lemma fmu_indicator_mul_indicator_eq
  [Group G]
  [MulAction G E]
  {A B : Set (ConfigSpace E)}
  {ω : ConfigSpace E} :
-- imply
  A.indicator (fun _ => (1:ℝ)) ω * B.indicator (fun _ => (1:ℝ)) ω = (A ∩ B).indicator (fun _ => (1:ℝ)) ω := by
-- proof
  apply StatMech.FK.fmu_indicator_mul_indicator A B ω

/--
[fmu_moInd_comp_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean)
-/
@[path]
private lemma fmu_moInd_comp_shift_eq
  [Group G]
  [MulAction G E]
  {g : G}
  {T : Finset E}
  {ω : ConfigSpace E} :
-- imply
  fmu_moInd T (shift g ω) = ((shift g : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T).indicator (fun _ => (1:ℝ)) ω := by
-- proof
  apply StatMech.FK.fmu_moInd_comp_shift g T ω

/--
[fmu_moInd_mul_shift_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean)
-/
@[path]
private lemma fmu_moInd_mul_shift_eq_eq
  [Group G]
  [MulAction G E]
  [Countable E]
  {g : G}
  {T T' : Finset E} :
-- imply
  (fun ω => fmu_moInd T ω * fmu_moInd T' (shift g ω)) = (fmu_multiOpen T ∩ (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T').indicator (fun _ => (1:ℝ)) := by
-- proof
  apply StatMech.FK.fmu_moInd_mul_shift_eq g T T'

/--
[fmu_integrable_moInd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean)
-/
@[path]
private lemma fmu_integrable_moInd_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  [Countable E]
  {T : Finset E} :
-- imply
  Integrable (fmu_moInd T) μ := by
-- proof
  apply StatMech.FK.fmu_integrable_moInd T

/--
[fmu_integrable_moInd_mul_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean)
-/
@[path]
private lemma fmu_integrable_moInd_mul_shift_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  [Countable E]
  {g : G}
  {T T' : Finset E} :
-- imply
  Integrable (fun ω => fmu_moInd T ω * fmu_moInd T' (shift g ω)) μ := by
-- proof
  apply StatMech.FK.fmu_integrable_moInd_mul_shift g T T'

/--
[fmu_integral_moInd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean)
-/
@[path]
private lemma fmu_integral_moInd_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  [Countable E]
  {T : Finset E} :
-- imply
  (∫ ω, fmu_moInd T ω ∂μ) = μ.real (fmu_multiOpen T) := by
-- proof
  apply StatMech.FK.fmu_integral_moInd T

/--
[fmu_traceInd_eq_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean)
-/
@[path]
private lemma fmu_traceInd_eq_prod_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  {F : Finset E}
  {τ : E → Bool}
  {ω : ConfigSpace E} :
-- imply
  fmu_traceInd F τ ω = ∏ e ∈ F, (if τ e then fmu_xR ω e else (1 - fmu_xR ω e)) := by
-- proof
  apply StatMech.FK.fmu_traceInd_eq_prod F τ ω

/--
[fmu_traceInd_expand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean)
-/
@[path]
private lemma fmu_traceInd_expand_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  [DecidableEq E]
  {F : Finset E}
  {τ : E → Bool}
  {ω : ConfigSpace E} :
-- imply
  fmu_traceInd F τ ω = ∑ T ∈ F.powerset, fmu_traceCoef F τ T * fmu_moInd T ω := by
-- proof
  apply StatMech.FK.fmu_traceInd_expand F τ ω

/--
[fmu_cylinder_indicator_eq_sum_traceInd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean)
-/
@[path]
private lemma fmu_cylinder_indicator_eq_sum_traceInd_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  [DecidableEq E]
  {F : Finset E}
  {Sf : Finset (↥F → Bool)}
  {ω : ConfigSpace E} :
-- imply
  (cylinder F (↑Sf : Set (↥F → Bool))).indicator (fun _ => (1:ℝ)) ω = ∑ σ ∈ Sf, fmu_traceInd F (fun e => if h : e ∈ F then σ ⟨e, h⟩ else false) ω := by
-- proof
  apply StatMech.FK.fmu_cylinder_indicator_eq_sum_traceInd F Sf ω

/--
[fmu_cylinder_expand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean)
-/
@[path]
private lemma fmu_cylinder_expand_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
-- given
  (hA : A ∈ measurableCylinders (fun _ : E => Bool)) :
-- imply
  ∃ (P : Finset (Finset E)) (c : Finset E → ℝ), ∀ ω, A.indicator (fun _ => (1:ℝ)) ω = ∑ T ∈ P, c T * fmu_moInd T ω := by
-- proof
  apply StatMech.FK.fmu_cylinder_expand A hA

/--
[fmu_real_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean)
-/
@[path]
private lemma fmu_real_eq_sum_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  [Countable E]
  {C : Set (ConfigSpace E)}
  {P : Finset (Finset E)}
  {c : Finset E → ℝ}
-- given
  (hC : MeasurableSet C)
  (hexp : ∀ ω, C.indicator (fun _ => (1:ℝ)) ω = ∑ T ∈ P, c T * fmu_moInd T ω) :
-- imply
  μ.real C = ∑ T ∈ P, c T * μ.real (fmu_multiOpen T) := by
-- proof
  apply StatMech.FK.fmu_real_eq_sum hC P c hexp

/--
[fmu_real_inter_shift_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean)
-/
@[path]
private lemma fmu_real_inter_shift_eq_sum_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  [Countable E]
  {g : G}
  {C : Set (ConfigSpace E)}
  {P : Finset (Finset E)}
  {c : Finset E → ℝ}
-- given
  (hC : MeasurableSet C)
  (hexp : ∀ ω, C.indicator (fun _ => (1:ℝ)) ω = ∑ T ∈ P, c T * fmu_moInd T ω) :
-- imply
  μ.real (C ∩ (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' C) = ∑ T ∈ P, ∑ T' ∈ P, c T * c T' * μ.real (fmu_multiOpen T ∩ (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T') := by
-- proof
  apply StatMech.FK.fmu_real_inter_shift_eq_sum g hC P c hexp

/--
[fmu_selfMixing_one_of_pairMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean)
-/
@[path]
private lemma fmu_selfMixing_one_of_pairMixing_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  [Countable E]
  {C : Set (ConfigSpace E)}
  {P : Finset (Finset E)}
  {c : Finset E → ℝ}
  {ε : ℝ}
-- given
  (hmix : fmu_PairMixing (G := G) μ)
  (hC : MeasurableSet C)
  (hexp : ∀ ω, C.indicator (fun _ => (1:ℝ)) ω = ∑ T ∈ P, c T * fmu_moInd T ω)
  (hε : 0 < ε) :
-- imply
  ∃ g : G, := by
-- proof
  apply StatMech.FK.fmu_selfMixing_one_of_pairMixing hmix hC P c hexp ε hε

/--
[fmu_selfMixing_of_pairMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean)
-/
@[path]
private lemma fmu_selfMixing_of_pairMixing_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  [Countable E]
-- given
  (hmix : fmu_PairMixing (G := G) μ) :
-- imply
  fmc_SelfMixing (G := G) μ := by
-- proof
  apply StatMech.FK.fmu_selfMixing_of_pairMixing hmix

/--
[fmu_isErgodic_of_pairMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean)
-/
@[path]
private lemma fmu_isErgodic_of_pairMixing_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  [Countable E]
-- given
  (hμ : IsTranslationInvariant (G := G) μ)
  (hmix : fmu_PairMixing (G := G) μ) :
-- imply
  IsErgodic (G := G) μ := by
-- proof
  apply StatMech.FK.fmu_isErgodic_of_pairMixing hμ hmix

/--
[fmu_dirac_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean)
-/
@[path]
private lemma fmu_dirac_mem_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  {g : G}
  {T T' : Finset E} :
-- imply
  (fun _ : E => true) ∈ fmu_multiOpen T ∩ (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T' := by
-- proof
  apply StatMech.FK.fmu_dirac_mem g T T'

/--
[fmu_pairMixing_dirac](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean)
-/
@[path]
private lemma fmu_pairMixing_dirac_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  [Countable E]
  [MeasurableSingletonClass (ConfigSpace E)] :
-- imply
  fmu_PairMixing (G := G) (Measure.dirac (fun _ : E => true)) := by
-- proof
  apply StatMech.FK.fmu_pairMixing_dirac

/--
[fmu_multiOpen_mem_measurableCylinders](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean)
-/
@[path]
private lemma fmu_multiOpen_mem_measurableCylinders_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  [DecidableEq E]
  {T : Finset E} :
-- imply
  fmu_multiOpen T ∈ measurableCylinders (fun _ : E => Bool) := by
-- proof
  apply StatMech.FK.fmu_multiOpen_mem_measurableCylinders T

/--
[fmu_pairMixing_of_genMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean)
-/
@[path]
private lemma fmu_pairMixing_of_genMixing_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  [DecidableEq E]
-- given
  (h : fmu_GenMixing (G := G) μ) :
-- imply
  fmu_PairMixing (G := G) μ := by
-- proof
  apply StatMech.FK.fmu_pairMixing_of_genMixing h

/--
[fmu_pair_fkg_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean)
-/
@[path]
private lemma fmu_pair_fkg_lower_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  [Countable E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  {g : G}
  {T T' : Finset E}
-- given
  (hμ : IsTranslationInvariant (G := G) μ)
  (hPA : ∀ {A B : Set (ConfigSpace E)}, IsIncreasing A → IsIncreasing B → MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B)) :
-- imply
  μ.real (fmu_multiOpen T) * μ.real (fmu_multiOpen T') ≤ μ.real (fmu_multiOpen T ∩ (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' fmu_multiOpen T') := by
-- proof
  apply StatMech.FK.fmu_pair_fkg_lower hμ hPA g T T'

/--
[fmu_pairMixing_of_upperDecay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean)
-/
@[path]
private lemma fmu_pairMixing_of_upperDecay_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  [Countable E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
-- given
  (hμ : IsTranslationInvariant (G := G) μ)
  (hPA : ∀ {A B : Set (ConfigSpace E)}, IsIncreasing A → IsIncreasing B → MeasurableSet A → MeasurableSet B → μ.real A * μ.real B ≤ μ.real (A ∩ B))
  (hup : fmu_UpperDecay (G := G) μ) :
-- imply
  fmu_PairMixing (G := G) μ := by
-- proof
  apply StatMech.FK.fmu_pairMixing_of_upperDecay hμ hPA hup

/--
[fmu_upperDecay_dirac](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean)
-/
@[path]
private lemma fmu_upperDecay_dirac_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  [Countable E]
  [MeasurableSingletonClass (ConfigSpace E)] :
-- imply
  fmu_UpperDecay (G := G) (Measure.dirac (fun _ : E => true)) := by
-- proof
  apply StatMech.FK.fmu_upperDecay_dirac

/--
[fmu_wiredIV_fkg_multiOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean)
-/
@[path]
private lemma fmu_wiredIV_fkg_multiOpen_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  {d : ℕ}
  {p : ℝ}
  {s₁ s₂ : Finset (Sym2 (Site d))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen s₁) * (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen s₂) ≤ (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (fmu_multiOpen s₁ ∩ fmu_multiOpen s₂) := by
-- proof
  apply StatMech.FK.fmu_wiredIV_fkg_multiOpen hp hp1 s₁ s₂

/--
[fmu_wiredIV_pairMixing_of_upperDecay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean)
-/
@[path]
private lemma fmu_wiredIV_pairMixing_of_upperDecay_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hup : fmu_UpperDecay (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))) :
-- imply
  fmu_PairMixing (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.fmu_wiredIV_pairMixing_of_upperDecay hp hp1 hup

/--
[fmu_wiredIV_isErgodic_of_pairMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean)
-/
@[path]
private lemma fmu_wiredIV_isErgodic_of_pairMixing_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hmix : fmu_PairMixing (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.fmu_wiredIV_isErgodic_of_pairMixing hp hp1 hmix

/--
[fmu_wiredIV_isErgodic_of_upperDecay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean)
-/
@[path]
private lemma fmu_wiredIV_isErgodic_of_upperDecay_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hup : fmu_UpperDecay (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.fmu_wiredIV_isErgodic_of_upperDecay hp hp1 hup

/--
[fmu_freeIV_isErgodic_of_pairMixing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKMixingUpperClose.lean)
-/
@[path]
private lemma fmu_freeIV_isErgodic_of_pairMixing_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hmix : fmu_PairMixing (G := Multiplicative (Site d)) (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (freeInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.fmu_freeIV_isErgodic_of_pairMixing hp hp1 hmix


-- created on 2026-10-23
