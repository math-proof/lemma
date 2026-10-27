import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalPerronDensity.Part6
open Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexPerronGaugeThreshold_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronDensity.lean)
-/
@[path]
private lemma sixVertexPerronGaugeThreshold_spec_eq
  {c : Real}
  {n : Nat}
-- given
  (hc : 2 < c)
  (hn : 0 < n) :
-- imply
  ∀ k ≥ sixVertexPerronGaugeThreshold hc n, ∃ p, SixVertexHalfFilledPerronGaugeWitness hc k ((1 : Real) / (n : Real) ^ 8) p := by
-- proof
  apply StatMech.FrontierD.sixVertexPerronGaugeThreshold_spec hc hn

/--
[sixVertexPerronGaugeThreshold_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronDensity.lean)
-/
@[path]
private lemma sixVertexPerronGaugeThreshold_zero_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexPerronGaugeThreshold hc 0 = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexPerronGaugeThreshold_zero hc

/--
[sixVertexPerronGaugeStage_le_eighthRoot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronDensity.lean)
-/
@[path]
private lemma sixVertexPerronGaugeStage_le_eighthRoot_eq
  {k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexPerronGaugeStage hc k ≤ Nat.sqrt (Nat.sqrt (Nat.sqrt (k + 1))) := by
-- proof
  apply StatMech.FrontierD.sixVertexPerronGaugeStage_le_eighthRoot hc k

/--
[sixVertexPerronGaugeStage_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronDensity.lean)
-/
@[path]
private lemma sixVertexPerronGaugeStage_le_eq
  {k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexPerronGaugeStage hc k ≤ k + 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexPerronGaugeStage_le hc k

/--
[sixVertexPerronGaugeStage_pow_eight_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronDensity.lean)
-/
@[path]
private lemma sixVertexPerronGaugeStage_pow_eight_le_eq
  {k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  (sixVertexPerronGaugeStage hc k) ^ 8 ≤ k + 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexPerronGaugeStage_pow_eight_le hc k

/--
[sixVertexPerronGaugeStage_threshold_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronDensity.lean)
-/
@[path]
private lemma sixVertexPerronGaugeStage_threshold_le_eq
  {c : Real}
  {k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexPerronGaugeThreshold hc (sixVertexPerronGaugeStage hc k) ≤ k := by
-- proof
  apply StatMech.FrontierD.sixVertexPerronGaugeStage_threshold_le hc k

/--
[tendsto_sixVertexPerronGaugeStage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronDensity.lean)
-/
@[path]
private lemma tendsto_sixVertexPerronGaugeStage_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (sixVertexPerronGaugeStage hc) atTop atTop := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexPerronGaugeStage hc

/--
[sixVertexCanonicalDensityPerronBetheRoots_mem_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronDensity.lean)
-/
@[path]
private lemma sixVertexCanonicalDensityPerronBetheRoots_mem_open_eq
  {c : Real}
  {k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  SixVertexOpenRootSimplex (sixVertexCanonicalDensityPerronBetheRoots hc k) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalDensityPerronBetheRoots_mem_open hc k

/--
[sixVertexCanonicalDensityPerronBetheRoots_is_solution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronDensity.lean)
-/
@[path]
private lemma sixVertexCanonicalDensityPerronBetheRoots_is_solution_eq
  {c : Real}
  {k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  SixVertexSatisfiesBetheEquations c (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (sixVertexCanonicalDensityPerronBetheRoots hc k) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalDensityPerronBetheRoots_is_solution hc k

/--
[eventually_sixVertexCanonicalDensityPerronBetheRoots_gaugeWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronDensity.lean)
-/
@[path]
private lemma eventually_sixVertexCanonicalDensityPerronBetheRoots_gaugeWitness_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, SixVertexHalfFilledPerronGaugeWitness hc k ((1 : Real) / (sixVertexPerronGaugeStage hc k : Real) ^ 8) (sixVertexCanonicalDensityPerronBetheRoots hc k) := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexCanonicalDensityPerronBetheRoots_gaugeWitness hc

/--
[eventually_sixVertexCanonicalDensityPerronGauge_lt_stagePow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronDensity.lean)
-/
@[path]
private lemma eventually_sixVertexCanonicalDensityPerronGauge_lt_stagePow_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, sixVertexCanonicalDensityPerronGauge hc k < (1 : Real) / (sixVertexPerronGaugeStage hc k : Real) ^ 8 := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexCanonicalDensityPerronGauge_lt_stagePow hc

/--
[tendsto_sixVertexCanonicalDensityPerronGauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronDensity.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalDensityPerronGauge_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (sixVertexCanonicalDensityPerronGauge hc) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalDensityPerronGauge hc

/--
[eventually_sixVertexCanonicalDensityPerronFiniteDensity_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronDensity.lean)
-/
@[path]
private lemma eventually_sixVertexCanonicalDensityPerronFiniteDensity_lower_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  ∃ lower : Real, 0 < lower ∧ ∀ᶠ k : Nat in atTop, ∀ x : Real, lower ≤ sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (sixVertexCanonicalDensityPerronBetheRoots hc k) x := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexCanonicalDensityPerronFiniteDensity_lower hc

/--
[eventually_sixVertexLambdaAlongFour_eq_canonicalDensityPerronValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronDensity.lean)
-/
@[path]
private lemma eventually_sixVertexLambdaAlongFour_eq_canonicalDensityPerronValue_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, sixVertexLambdaAlongFour c 0 k = sixVertexSymmetricBetheEigenvalueValue c (sixVertexCanonicalDensityPerronPositiveHalfRoots hc k) := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexLambdaAlongFour_eq_canonicalDensityPerronValue hc

/--
[abs_sixVertexCanonicalDensityIntegral_sub_fourier_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronDensity.lean)
-/
@[path]
private lemma abs_sixVertexCanonicalDensityIntegral_sub_fourier_le_eq
  {c : Real}
  {f : Real → Real}
  {B : Real}
  {k : Nat}
-- given
  (hc : 2 < c)
  (hf : Continuous f)
  (hB : 0 ≤ B)
  (hfBound : ∀ x ∈ Set.Icc (-Real.pi) Real.pi, |f x| ≤ B) :
-- imply
  |(∫ y in -Real.pi..Real.pi, f y * sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (sixVertexCanonicalDensityPerronBetheRoots hc k) y) - ∫ y in -Real.pi..Real.pi, f y * sixVertexFourierPhysicalDensity c hc y| ≤ B * (sixVertexCanonicalDensityPerronGauge hc k / ((sixVertexAnisotropyMagnitude c - 1) / sixVertexRootDensityScale c)) * (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexCanonicalDensityIntegral_sub_fourier_le hc hf hB hfBound k

/--
[tendsto_sixVertexCanonicalDensityPerronEmpiricalObservable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalPerronDensity.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalDensityPerronEmpiricalObservable_eq
  {c : Real}
  {f : Real → Real}
  {C : NNReal}
  {B : Real}
-- given
  (hc : 2 < c)
  (hf : Continuous f)
  (hlip : LipschitzWith C f)
  (hperiodic : Function.Periodic f (2 * Real.pi))
  (hB : 0 ≤ B)
  (hfBound : ∀ x ∈ Set.Icc (-Real.pi) Real.pi, |f x| ≤ B) :
-- imply
  Tendsto (sixVertexCanonicalDensityPerronEmpiricalObservable hc f) atTop (nhds (∫ y in -Real.pi..Real.pi, f y * sixVertexFourierPhysicalDensity c hc y)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalDensityPerronEmpiricalObservable hc hf hlip hperiodic hB hfBound


-- created on 2026-10-23
