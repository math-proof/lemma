import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.GibbsChoquet
open MeasureTheory ProbabilityTheory MeasurableSpace Set StatMech StatMech.Ising


/--
[upTrue_isUpperSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsChoquet.lean)
-/
@[path]
private lemma upTrue_isUpperSet_eq
  {d : ℕ}
  {x : E} :
-- imply
  IsUpperSet {ω : ConfigSpace E | ω x = true} := by
-- proof
  apply StatMech.Ising.upTrue_isUpperSet x

/--
[upTrue_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsChoquet.lean)
-/
@[path]
private lemma upTrue_measurableSet_eq
  {d : ℕ}
  {x : E} :
-- imply
  MeasurableSet {ω : ConfigSpace E | ω x = true} := by
-- proof
  apply StatMech.Ising.upTrue_measurableSet x

/--
[upTrue_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsChoquet.lean)
-/
@[path]
private lemma upTrue_mem_eq
  {d : ℕ}
  {x : E} :
-- imply
  {ω : ConfigSpace E | ω x = true} ∈ upMeasSystem E := by
-- proof
  apply StatMech.Ising.upTrue_mem x

/--
[isPiSystem_upMeas](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsChoquet.lean)
-/
@[path]
private lemma isPiSystem_upMeas_eq
  {d : ℕ} :
-- imply
  IsPiSystem (upMeasSystem E) := by
-- proof
  apply StatMech.Ising.isPiSystem_upMeas

/--
[generateFrom_upMeas](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsChoquet.lean)
-/
@[path]
private lemma generateFrom_upMeas_eq
  {d : ℕ} :
-- imply
  MeasurableSpace.generateFrom (upMeasSystem E) = (inferInstance : MeasurableSpace (ConfigSpace E)) := by
-- proof
  apply StatMech.Ising.generateFrom_upMeas

/--
[StochasticallyDominated.antisymm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsChoquet.lean)
-/
@[path]
private lemma antisymm_eq
  {d : ℕ}
  {μ ν : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  [IsProbabilityMeasure ν]
-- given
  (h₁ : μ ≼ ν)
  (h₂ : ν ≼ μ) :
-- imply
  μ = ν := by
-- proof
  apply StatMech.Ising.StochasticallyDominated.antisymm h₁ h₂

/--
[gibbs_unique_of_phases_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsChoquet.lean)
-/
@[path]
private lemma gibbs_unique_of_phases_eq_eq
  {d : ℕ}
  {μm μp μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μm]
  [IsProbabilityMeasure μp]
  [IsProbabilityMeasure μ]
-- given
  (hsw₁ : μm ≼ μ)
  (hsw₂ : μ ≼ μp)
  (hphase : μp = μm) :
-- imply
  μ = μm := by
-- proof
  apply StatMech.Ising.gibbs_unique_of_phases_eq hsw₁ hsw₂ hphase

/--
[gibbs_sandwiched_eq_of_phases_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsChoquet.lean)
-/
@[path]
private lemma gibbs_sandwiched_eq_of_phases_eq_eq
  {d : ℕ}
  {μm μp μ μ' : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μm]
  [IsProbabilityMeasure μp]
  [IsProbabilityMeasure μ]
  [IsProbabilityMeasure μ']
-- given
  (hsw₁ : μm ≼ μ)
  (hsw₂ : μ ≼ μp)
  (hsw₁' : μm ≼ μ')
  (hsw₂' : μ' ≼ μp)
  (hphase : μp = μm) :
-- imply
  μ = μ' := by
-- proof
  apply StatMech.Ising.gibbs_sandwiched_eq_of_phases_eq hsw₁ hsw₂ hsw₁' hsw₂' hphase

/--
[gibbsMix_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsChoquet.lean)
-/
@[path]
private lemma gibbsMix_apply_eq
  {d : ℕ}
  {μm μp : Measure (ConfigSpace E)}
  {s : Set (ConfigSpace E)}
-- given
  (a b : ℝ≥0∞) :
-- imply
  gibbsMix a b μm μp s = a * μm s + b * μp s := by
-- proof
  apply StatMech.Ising.gibbsMix_apply a b μm μp s

/--
[gibbsMix_one_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsChoquet.lean)
-/
@[path]
private lemma gibbsMix_one_zero_eq
  {d : ℕ}
  {μm μp : Measure (ConfigSpace E)} :
-- imply
  gibbsMix 1 0 μm μp = μm := by
-- proof
  apply StatMech.Ising.gibbsMix_one_zero μm μp

/--
[gibbsMix_zero_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsChoquet.lean)
-/
@[path]
private lemma gibbsMix_zero_one_eq
  {d : ℕ}
  {μm μp : Measure (ConfigSpace E)} :
-- imply
  gibbsMix 0 1 μm μp = μp := by
-- proof
  apply StatMech.Ising.gibbsMix_zero_one μm μp

/--
[isDLRState_gibbsMix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsChoquet.lean)
-/
@[path]
private lemma isDLRState_gibbsMix_eq
  {d : ℕ}
  {a b : ℝ≥0∞}
  {μm μp : Measure (ConfigSpace (Site d))}
  [IsFiniteMeasure μm]
  [IsFiniteMeasure μp]
  [IsFiniteMeasure (gibbsMix a b μm μp)]
-- given
  (β h : ℝ)
  (hab : a + b = 1)
  (h₁ : IsDLRState d β h μm)
  (h₂ : IsDLRState d β h μp) :
-- imply
  IsDLRState d β h (gibbsMix a b μm μp) := by
-- proof
  apply StatMech.Ising.isDLRState_gibbsMix β h hab μm μp h₁ h₂

/--
[gibbsMix_isProbabilityMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsChoquet.lean)
-/
@[path]
private lemma gibbsMix_isProbabilityMeasure_eq
  {d : ℕ}
  {a b : ℝ≥0∞}
  {μm μp : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μm]
  [IsProbabilityMeasure μp]
-- given
  (hab : a + b = 1) :
-- imply
  IsProbabilityMeasure (gibbsMix a b μm μp) := by
-- proof
  apply StatMech.Ising.gibbsMix_isProbabilityMeasure hab μm μp

/--
[exists_real_ne_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsChoquet.lean)
-/
@[path]
private lemma exists_real_ne_of_ne_eq
  {d : ℕ}
  {μm μp : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μm]
  [IsProbabilityMeasure μp]
-- given
  (hne : μm ≠ μp) :
-- imply
  ∃ A, MeasurableSet A ∧ μm.real A ≠ μp.real A := by
-- proof
  apply StatMech.Ising.exists_real_ne_of_ne hne

/--
[gibbsMix_coeff_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsChoquet.lean)
-/
@[path]
private lemma gibbsMix_coeff_unique_eq
  {d : ℕ}
  {μm μp : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μm]
  [IsProbabilityMeasure μp]
  {a b a' b' : ℝ≥0∞}
-- given
  (hne : μm ≠ μp)
  (ha : a ≠ ⊤)
  (hb : b ≠ ⊤)
  (ha' : a' ≠ ⊤)
  (hb' : b' ≠ ⊤)
  (hab : a + b = 1)
  (hab' : a' + b' = 1)
  (heq : gibbsMix a b μm μp = gibbsMix a' b' μm μp) :
-- imply
  a = a' := by
-- proof
  apply StatMech.Ising.gibbsMix_coeff_unique hne ha hb ha' hb' hab hab' heq

/--
[gibbsMix_coeff_unique_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsChoquet.lean)
-/
@[path]
private lemma gibbsMix_coeff_unique_pair_eq
  {d : ℕ}
  {μm μp : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μm]
  [IsProbabilityMeasure μp]
  {a b a' b' : ℝ≥0∞}
-- given
  (hne : μm ≠ μp)
  (ha : a ≠ ⊤)
  (hb : b ≠ ⊤)
  (ha' : a' ≠ ⊤)
  (hb' : b' ≠ ⊤)
  (hab : a + b = 1)
  (hab' : a' + b' = 1)
  (heq : gibbsMix a b μm μp = gibbsMix a' b' μm μp) :
-- imply
  a = a' ∧ b = b' := by
-- proof
  apply StatMech.Ising.gibbsMix_coeff_unique_pair hne ha hb ha' hb' hab hab' heq

/--
[gibbsMix_ne_minus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsChoquet.lean)
-/
@[path]
private lemma gibbsMix_ne_minus_eq
  {d : ℕ}
  {μm μp : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μm]
  [IsProbabilityMeasure μp]
  {a b : ℝ≥0∞}
-- given
  (hne : μm ≠ μp)
  (ha : a ≠ ⊤)
  (hb : b ≠ ⊤)
  (hab : a + b = 1)
  (hb0 : b ≠ 0) :
-- imply
  gibbsMix a b μm μp ≠ μm := by
-- proof
  apply StatMech.Ising.gibbsMix_ne_minus hne ha hb hab hb0

/--
[gibbsMix_ne_plus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsChoquet.lean)
-/
@[path]
private lemma gibbsMix_ne_plus_eq
  {d : ℕ}
  {μm μp : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μm]
  [IsProbabilityMeasure μp]
  {a b : ℝ≥0∞}
-- given
  (hne : μm ≠ μp)
  (ha : a ≠ ⊤)
  (hb : b ≠ ⊤)
  (hab : a + b = 1)
  (ha0 : a ≠ 0) :
-- imply
  gibbsMix a b μm μp ≠ μp := by
-- proof
  apply StatMech.Ising.gibbsMix_ne_plus hne ha hb hab ha0

/--
[minusState_extreme_in_segment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsChoquet.lean)
-/
@[path]
private lemma minusState_extreme_in_segment_eq
  {d : ℕ}
  {μm μp : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μm]
  [IsProbabilityMeasure μp]
  {a b : ℝ≥0∞}
-- given
  (hne : μm ≠ μp)
  (ha : a ≠ ⊤)
  (hb : b ≠ ⊤)
  (hab : a + b = 1)
  (heq : gibbsMix a b μm μp = μm) :
-- imply
  a = 1 ∧ b = 0 := by
-- proof
  apply StatMech.Ising.minusState_extreme_in_segment hne ha hb hab heq

/--
[plusState_extreme_in_segment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsChoquet.lean)
-/
@[path]
private lemma plusState_extreme_in_segment_eq
  {d : ℕ}
  {μm μp : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μm]
  [IsProbabilityMeasure μp]
  {a b : ℝ≥0∞}
-- given
  (hne : μm ≠ μp)
  (ha : a ≠ ⊤)
  (hb : b ≠ ⊤)
  (hab : a + b = 1)
  (heq : gibbsMix a b μm μp = μp) :
-- imply
  a = 0 ∧ b = 1 := by
-- proof
  apply StatMech.Ising.plusState_extreme_in_segment hne ha hb hab heq

/--
[gibbsMix_param_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsChoquet.lean)
-/
@[path]
private lemma gibbsMix_param_injective_eq
  {d : ℕ}
  {μm μp : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μm]
  [IsProbabilityMeasure μp]
  {a a' : ℝ≥0∞}
-- given
  (hne : μm ≠ μp)
  (ha : a ≤ 1)
  (ha' : a' ≤ 1)
  (heq : gibbsMix a (1 - a) μm μp = gibbsMix a' (1 - a') μm μp) :
-- imply
  a = a' := by
-- proof
  apply StatMech.Ising.gibbsMix_param_injective hne ha ha' heq


-- created on 2026-10-23
