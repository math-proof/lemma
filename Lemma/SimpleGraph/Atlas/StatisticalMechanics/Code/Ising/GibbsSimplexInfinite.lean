import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplexInfinite.Part3
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology StatMech StatMech.Ising


/--
[gsi_dlr_real_eq_integral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplexInfinite.lean)
-/
@[path]
private lemma gsi_dlr_real_eq_integral_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure μ]
  {n : ℕ}
  {A : Set (ConfigSpace (Site d))}
-- given
  (β h : ℝ)
  (hμ : IsDLRState d β h μ)
  (hA : MeasurableSet A) :
-- imply
  μ.real A = ∫ ω, (fvMeasure ω n (bondFinsetTouch d n) β h).real A ∂μ := by
-- proof
  apply StatMech.Ising.gsi_dlr_real_eq_integral β h μ hμ n hA

/--
[fvMeasure_real_integrable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplexInfinite.lean)
-/
@[path]
private lemma fvMeasure_real_integrable_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure μ]
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {A : Set (ConfigSpace (Site d))}
-- given
  (β h : ℝ)
  (hA : MeasurableSet A) :
-- imply
  Integrable (fun ω => (fvMeasure ω n B β h).real A) μ := by
-- proof
  apply StatMech.Ising.fvMeasure_real_integrable β h μ n B hA

/--
[gsi_dlr_real_le_plusMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplexInfinite.lean)
-/
@[path]
private lemma gsi_dlr_real_le_plusMeasure_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure μ]
  {n : ℕ}
  {A : Set (ConfigSpace (Site d))}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hμ : IsDLRState d β h μ)
  (hA : MeasurableSet A)
  (hAinc : IsIncreasing A) :
-- imply
  μ.real A ≤ (plusMeasure d n β h : Measure (ConfigSpace (Site d))).real A := by
-- proof
  apply StatMech.Ising.gsi_dlr_real_le_plusMeasure β h hβ hh μ hμ n hA hAinc

/--
[gsi_minusMeasure_le_dlr_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplexInfinite.lean)
-/
@[path]
private lemma gsi_minusMeasure_le_dlr_real_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure μ]
  {n : ℕ}
  {A : Set (ConfigSpace (Site d))}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hμ : IsDLRState d β h μ)
  (hA : MeasurableSet A)
  (hAinc : IsIncreasing A) :
-- imply
  (minusMeasure d n β h : Measure (ConfigSpace (Site d))).real A ≤ μ.real A := by
-- proof
  apply StatMech.Ising.gsi_minusMeasure_le_dlr_real β h hβ hh μ hμ n hA hAinc

/--
[gsi_dlr_le_plusState_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplexInfinite.lean)
-/
@[path]
private lemma gsi_dlr_le_plusState_closed_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure μ]
  {A : Set (ConfigSpace (Site d))}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hμ : IsDLRState d β h μ)
  (hAcl : IsClosed A)
  (hAinc : IsIncreasing A) :
-- imply
  μ.real A ≤ (plusState d β h : Measure (ConfigSpace (Site d))).real A := by
-- proof
  apply StatMech.Ising.gsi_dlr_le_plusState_closed β h hβ hh μ hμ hAcl hAinc

/--
[gsi_minusState_le_dlr_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplexInfinite.lean)
-/
@[path]
private lemma gsi_minusState_le_dlr_open_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure μ]
  {A : Set (ConfigSpace (Site d))}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hμ : IsDLRState d β h μ)
  (hAop : IsOpen A)
  (hAinc : IsIncreasing A) :
-- imply
  (minusState d β h : Measure (ConfigSpace (Site d))).real A ≤ μ.real A := by
-- proof
  apply StatMech.Ising.gsi_minusState_le_dlr_open β h hβ hh μ hμ hAop hAinc

/--
[StochasticallyDominatedClopen.refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplexInfinite.lean)
-/
@[path]
private lemma refl_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace E)} :
-- imply
  μ ≼c μ := by
-- proof
  apply StatMech.Ising.StochasticallyDominatedClopen.refl μ

/--
[StochasticallyDominatedClopen.trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplexInfinite.lean)
-/
@[path]
private lemma trans_eq
  {d : ℕ}
  {μ ν ρ : Measure (ConfigSpace E)}
-- given
  (h₁ : μ ≼c ν)
  (h₂ : ν ≼c ρ) :
-- imply
  μ ≼c ρ := by
-- proof
  apply StatMech.Ising.StochasticallyDominatedClopen.trans h₁ h₂

/--
[StochasticallyDominated.toClopen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplexInfinite.lean)
-/
@[path]
private lemma toClopen_eq
  {d : ℕ}
  [Countable E]
  {μ ν : Measure (ConfigSpace E)}
-- given
  (h : μ ≼ ν) :
-- imply
  μ ≼c ν := by
-- proof
  apply StatMech.Ising.StochasticallyDominated.toClopen h

/--
[gsi_infinite_volume_sandwich](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplexInfinite.lean)
-/
@[path]
private lemma gsi_infinite_volume_sandwich_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure μ]
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hμ : IsDLRState d β h μ) :
-- imply
  (minusState d β h : Measure (ConfigSpace (Site d))) ≼c μ ∧ μ ≼c (plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.gsi_infinite_volume_sandwich β h hβ hh μ hμ

/--
[isPiSystem_clopenUp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplexInfinite.lean)
-/
@[path]
private lemma isPiSystem_clopenUp_eq
  {d : ℕ} :
-- imply
  IsPiSystem (clopenUpSystem E) := by
-- proof
  apply StatMech.Ising.isPiSystem_clopenUp

/--
[upTrue_isClopen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplexInfinite.lean)
-/
@[path]
private lemma upTrue_isClopen_eq
  {d : ℕ}
  {x : E} :
-- imply
  IsClopen {ω : ConfigSpace E | ω x = true} := by
-- proof
  apply StatMech.Ising.upTrue_isClopen x

/--
[upTrue_mem_clopen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplexInfinite.lean)
-/
@[path]
private lemma upTrue_mem_clopen_eq
  {d : ℕ}
  {x : E} :
-- imply
  {ω : ConfigSpace E | ω x = true} ∈ clopenUpSystem E := by
-- proof
  apply StatMech.Ising.upTrue_mem_clopen x

/--
[generateFrom_clopenUp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplexInfinite.lean)
-/
@[path]
private lemma generateFrom_clopenUp_eq
  {d : ℕ}
  [Countable E] :
-- imply
  MeasurableSpace.generateFrom (clopenUpSystem E) = (inferInstance : MeasurableSpace (ConfigSpace E)) := by
-- proof
  apply StatMech.Ising.generateFrom_clopenUp

/--
[gsi_clopen_antisymm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplexInfinite.lean)
-/
@[path]
private lemma gsi_clopen_antisymm_eq
  {d : ℕ}
  [Countable E]
  {μ ν : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  [IsProbabilityMeasure ν]
-- given
  (h₁ : μ ≼c ν)
  (h₂ : ν ≼c μ) :
-- imply
  μ = ν := by
-- proof
  apply StatMech.Ising.gsi_clopen_antisymm h₁ h₂

/--
[gsi_gibbs_unique_of_phases_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplexInfinite.lean)
-/
@[path]
private lemma gsi_gibbs_unique_of_phases_eq_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure μ]
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hμ : IsDLRState d β h μ)
  (hphase : (plusState d β h : Measure (ConfigSpace (Site d))) = (minusState d β h : Measure (ConfigSpace (Site d)))) :
-- imply
  μ = (minusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.gsi_gibbs_unique_of_phases_eq β h hβ hh μ hμ hphase


-- created on 2026-10-23
