import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.IsingPlusTIClose.Part5
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology BoundedContinuousFunction StatMech StatMech.Ising


/--
[iti_glue_plusField_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIClose.lean)
-/
@[path]
private lemma iti_glue_plusField_le_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (σ : {x // x ∈ box d n} → Bool) :
-- imply
  glue (plusField d) σ ≤ plusField d := by
-- proof
  apply StatMech.Ising.iti_glue_plusField_le σ

/--
[iti_crossbox_dom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIClose.lean)
-/
@[path]
private lemma iti_crossbox_dom_eq
  {d : ℕ}
  {n m : ℕ}
  {β : ℝ}
  {h : ℝ}
  {A : Set (ConfigSpace (Site d))}
-- given
  (hnm : n ≤ m)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hAmeas : MeasurableSet A)
  (hAinc : IsIncreasing A) :
-- imply
  (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real A ≤ (plusMeasure d n β h : Measure (ConfigSpace (Site d))).real A := by
-- proof
  apply StatMech.Ising.iti_crossbox_dom n m hnm hβ hh hAmeas hAinc

/--
[iti_plus_multiOpen_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIClose.lean)
-/
@[path]
private lemma iti_plus_multiOpen_antitone_eq
  {d : ℕ}
  {β : ℝ}
  {h : ℝ}
  {T : Finset (Site d)}
  {n m : ℕ}
-- given
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hnm : n ≤ m) :
-- imply
  (plusMeasure d m β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen (E := Site d) T) ≤ (plusMeasure d n β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen (E := Site d) T) := by
-- proof
  apply StatMech.Ising.iti_plus_multiOpen_antitone hβ hh T hnm

/--
[iti_prod_coordCM_eq_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIClose.lean)
-/
@[path]
private lemma iti_prod_coordCM_eq_indicator_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {ω : ConfigSpace (Site d)} :
-- imply
  (∏ x ∈ T, pstc_coordCM x ω) = (fmu_multiOpen (E := Site d) T).indicator (fun _ => (1:ℝ)) ω := by
-- proof
  apply StatMech.Ising.iti_prod_coordCM_eq_indicator T ω

/--
[iti_monomialCM_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIClose.lean)
-/
@[path]
private lemma iti_monomialCM_apply_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {ω : ConfigSpace (Site d)} :
-- imply
  iti_monomialCM T ω = (fmu_multiOpen (E := Site d) T).indicator (fun _ => (1:ℝ)) ω := by
-- proof
  apply StatMech.Ising.iti_monomialCM_apply T ω

/--
[iti_monomialCM_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIClose.lean)
-/
@[path]
private lemma iti_monomialCM_empty_eq
  {d : ℕ} :
-- imply
  iti_monomialCM (∅ : Finset (Site d)) = 1 := by
-- proof
  apply StatMech.Ising.iti_monomialCM_empty

/--
[iti_monomialCM_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIClose.lean)
-/
@[path]
private lemma iti_monomialCM_singleton_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  iti_monomialCM ({x} : Finset (Site d)) = pstc_coordCM x := by
-- proof
  apply StatMech.Ising.iti_monomialCM_singleton x

/--
[iti_monomialCM_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIClose.lean)
-/
@[path]
private lemma iti_monomialCM_mul_eq
  {d : ℕ}
  {T₁ T₂ : Finset (Site d)} :
-- imply
  iti_monomialCM T₁ * iti_monomialCM T₂ = iti_monomialCM (T₁ ∪ T₂) := by
-- proof
  apply StatMech.Ising.iti_monomialCM_mul T₁ T₂

/--
[iti_closure_isMonomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIClose.lean)
-/
@[path]
private lemma iti_closure_isMonomial_eq
  {d : ℕ}
  {hh : C(ConfigSpace (Site d), ℝ)}
-- given
  (hmem : hh ∈ Submonoid.closure (Set.range (pstc_coordCM (d := d)))) :
-- imply
  ∃ T : Finset (Site d), hh = iti_monomialCM T := by
-- proof
  apply StatMech.Ising.iti_closure_isMonomial hmem

/--
[iti_integral_monomialBcf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIClose.lean)
-/
@[path]
private lemma iti_integral_monomialBcf_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {μ : Measure (ConfigSpace (Site d))}
  [IsFiniteMeasure μ] :
-- imply
  (∫ ω, iti_monomialBcf T ω ∂μ) = μ.real (fmu_multiOpen (E := Site d) T) := by
-- proof
  apply StatMech.Ising.iti_integral_monomialBcf T μ

/--
[iti_monomialBcf_comp_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIClose.lean)
-/
@[path]
private lemma iti_monomialBcf_comp_shift_eq
  {d : ℕ}
  {T : Finset (Site d)}
  {g : Multiplicative (Site d)}
  {ω : ConfigSpace (Site d)} :
-- imply
  iti_monomialBcf T (shift g ω) = iti_monomialBcf (T.image (fun x => g⁻¹ • x)) ω := by
-- proof
  apply StatMech.Ising.iti_monomialBcf_comp_shift T g ω

/--
[iti_decayFun_monomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIClose.lean)
-/
@[path]
private lemma iti_decayFun_monomial_eq
  {d : ℕ}
  {μ : ℕ → ProbabilityMeasure (ConfigSpace (Site d))}
  {g : Multiplicative (Site d)}
  {T : Finset (Site d)}
  {n : ℕ} :
-- imply
  pstc_decayFun μ g (iti_monomialBcf T) n = ((μ n : Measure (ConfigSpace (Site d))).real (fmu_multiOpen (E := Site d) T)) - ((μ n : Measure (ConfigSpace (Site d))).real (fmu_multiOpen (E := Site d) (T.image (fun x => g⁻¹ • x)))) := by
-- proof
  apply StatMech.Ising.iti_decayFun_monomial μ g T n

/--
[iti_plus_multiOpen_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIClose.lean)
-/
@[path]
private lemma iti_plus_multiOpen_tendsto_eq
  {d : ℕ}
  {φ : ℕ → ℕ}
  {T : Finset (Site d)}
-- given
  (β h : ℝ)
  (hconv : WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h)) :
-- imply
  Tendsto (fun n => (plusMeasure d (φ n) β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen (E := Site d) T)) atTop (𝓝 ((plusState d β h : Measure (ConfigSpace (Site d))).real (fmu_multiOpen (E := Site d) T))) := by
-- proof
  apply StatMech.Ising.iti_plus_multiOpen_tendsto β h φ T hconv

/--
[iti_plusMultiHomogeneous_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIClose.lean)
-/
@[path]
private lemma iti_plusMultiHomogeneous_one_eq
  {d : ℕ}
-- given
  (β h : ℝ) :
-- imply
  iti_PlusMultiHomogeneous β h (1 : Multiplicative (Site d)) := by
-- proof
  apply StatMech.Ising.iti_plusMultiHomogeneous_one β h

/--
[iti_decayFun_monomial_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIClose.lean)
-/
@[path]
private lemma iti_decayFun_monomial_tendsto_zero_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {φ : ℕ → ℕ}
  {T : Finset (Site d)}
-- given
  (β h : ℝ)
  (hconv : WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h))
  (hhom : iti_PlusMultiHomogeneous β h g) :
-- imply
  Tendsto (pstc_decayFun (fun n => plusMeasure d (φ n) β h) g (iti_monomialBcf T)) atTop (𝓝 0) := by
-- proof
  apply StatMech.Ising.iti_decayFun_monomial_tendsto_zero β h g φ hconv hhom T

/--
[iti_decayFun_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIClose.lean)
-/
@[path]
private lemma iti_decayFun_add_eq
  {d : ℕ}
  {μ : ℕ → ProbabilityMeasure (ConfigSpace (Site d))}
  {g : Multiplicative (Site d)}
  {f f' : ConfigSpace (Site d) →ᵇ ℝ}
  {n : ℕ} :
-- imply
  pstc_decayFun μ g (f + f') n = pstc_decayFun μ g f n + pstc_decayFun μ g f' n := by
-- proof
  apply StatMech.Ising.iti_decayFun_add μ g f f' n

/--
[iti_decayFun_smul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIClose.lean)
-/
@[path]
private lemma iti_decayFun_smul_eq
  {d : ℕ}
  {μ : ℕ → ProbabilityMeasure (ConfigSpace (Site d))}
  {g : Multiplicative (Site d)}
  {c : ℝ}
  {f : ConfigSpace (Site d) →ᵇ ℝ}
  {n : ℕ} :
-- imply
  pstc_decayFun μ g (c • f) n = c * pstc_decayFun μ g f n := by
-- proof
  apply StatMech.Ising.iti_decayFun_smul μ g c f n

/--
[iti_decayFun_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIClose.lean)
-/
@[path]
private lemma iti_decayFun_zero_eq
  {d : ℕ}
  {μ : ℕ → ProbabilityMeasure (ConfigSpace (Site d))}
  {g : Multiplicative (Site d)}
  {n : ℕ} :
-- imply
  pstc_decayFun μ g (0 : ConfigSpace (Site d) →ᵇ ℝ) n = 0 := by
-- proof
  apply StatMech.Ising.iti_decayFun_zero μ g n

/--
[iti_cylinderAlg_le_decaySet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIClose.lean)
-/
@[path]
private lemma iti_cylinderAlg_le_decaySet_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {φ : ℕ → ℕ}
-- given
  (β h : ℝ)
  (hconv : WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h))
  (hhom : iti_PlusMultiHomogeneous β h g) :
-- imply
  Subalgebra.toSubmodule (pstc_cylinderAlg d) ≤ iti_decaySet β h g φ := by
-- proof
  apply StatMech.Ising.iti_cylinderAlg_le_decaySet β h g φ hconv hhom

/--
[iti_plusCylinderDecay_of_homogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIClose.lean)
-/
@[path]
private lemma iti_plusCylinderDecay_of_homogeneous_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {φ : ℕ → ℕ}
-- given
  (β h : ℝ)
  (hconv : WeakConvergesTo (fun n => plusMeasure d (φ n) β h) (plusState d β h))
  (hhom : iti_PlusMultiHomogeneous β h g) :
-- imply
  pstc_PlusCylinderDecay β h g φ := by
-- proof
  apply StatMech.Ising.iti_plusCylinderDecay_of_homogeneous β h g φ hconv hhom

/--
[iti_plusState_isTranslationInvariant_of_homogeneous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIClose.lean)
-/
@[path]
private lemma iti_plusState_isTranslationInvariant_of_homogeneous_eq
  {d : ℕ}
-- given
  (β h : ℝ)
  (hhom : ∀ g : Multiplicative (Site d), iti_PlusMultiHomogeneous β h g) :
-- imply
  ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.iti_plusState_isTranslationInvariant_of_homogeneous β h hhom

/--
[iti_plusState_isErgodic_of_homogeneous_upperDecay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIClose.lean)
-/
@[path]
private lemma iti_plusState_isErgodic_of_homogeneous_upperDecay_eq
  {d : ℕ}
  {β : ℝ}
-- given
  (hβ : 0 ≤ β)
  (h : ℝ)
  (hhom : ∀ g : Multiplicative (Site d), iti_PlusMultiHomogeneous β h g)
  (hup : fmu_UpperDecay (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d)))) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.iti_plusState_isErgodic_of_homogeneous_upperDecay hβ h hhom hup

/--
[iti_plusState_isInvariantExtremePoint_of_homogeneous_upperDecay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/IsingPlusTIClose.lean)
-/
@[path]
private lemma iti_plusState_isInvariantExtremePoint_of_homogeneous_upperDecay_eq
  {d : ℕ}
  {β : ℝ}
-- given
  (hβ : 0 ≤ β)
  (h : ℝ)
  (hhom : ∀ g : Multiplicative (Site d), iti_PlusMultiHomogeneous β h g)
  (hup : fmu_UpperDecay (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d)))) :
-- imply
  StatMech.FK.IsInvariantExtremePoint (G := Multiplicative (Site d)) (plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.iti_plusState_isInvariantExtremePoint_of_homogeneous_upperDecay hβ h hhom hup


-- created on 2026-10-23
