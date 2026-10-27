import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Probability.InfiniteHarris.Part3
open MeasureTheory Set Filter StatMech


/--
[ih_event_dependsOn_of_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InfiniteHarris.lean)
-/
@[path]
private lemma ih_event_dependsOn_of_indicator_eq
  [Countable E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {S : Set E}
-- given
  (h : _root_.DependsOn (A.indicator (fun _ => (1 : ℝ))) S) :
-- imply
  StatMech.DependsOn A S := by
-- proof
  apply StatMech.ih_event_dependsOn_of_indicator h

/--
[ih_indicator_dependsOn_of_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InfiniteHarris.lean)
-/
@[path]
private lemma ih_indicator_dependsOn_of_event_eq
  [Countable E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {S : Set E}
-- given
  (h : StatMech.DependsOn A S) :
-- imply
  _root_.DependsOn (A.indicator (fun _ => (1 : ℝ))) S := by
-- proof
  apply StatMech.ih_indicator_dependsOn_of_event h

/--
[ih_dependsOn_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InfiniteHarris.lean)
-/
@[path]
private lemma ih_dependsOn_inter_eq
  [Countable E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {S : Set E}
-- given
  (hA : StatMech.DependsOn A S)
  (hB : StatMech.DependsOn B S) :
-- imply
  StatMech.DependsOn (A ∩ B) S := by
-- proof
  apply StatMech.ih_dependsOn_inter hA hB

/--
[ih_dependsOn_iUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InfiniteHarris.lean)
-/
@[path]
private lemma ih_dependsOn_iUnion_eq
  [Countable E]
  [DecidableEq E]
  {S : Set E}
  {A : ι → Set (ConfigSpace E)}
-- given
  (hA : ∀ i, StatMech.DependsOn (A i) S) :
-- imply
  StatMech.DependsOn (⋃ i, A i) S := by
-- proof
  apply StatMech.ih_dependsOn_iUnion hA

/--
[ih_fill_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InfiniteHarris.lean)
-/
@[path]
private lemma ih_fill_mono_eq
  [Countable E]
  [DecidableEq E]
  {F : Finset E} :
-- imply
  Monotone (ih_fill F) := by
-- proof
  apply StatMech.ih_fill_mono F

/--
[ih_section_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InfiniteHarris.lean)
-/
@[path]
private lemma ih_section_isIncreasing_eq
  [Countable E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {F : Finset E}
-- given
  (hA : IsIncreasing A) :
-- imply
  IsIncreasing (ih_section A F) := by
-- proof
  apply StatMech.ih_section_isIncreasing hA F

/--
[ih_eq_cylinder_of_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InfiniteHarris.lean)
-/
@[path]
private lemma ih_eq_cylinder_of_dependsOn_eq
  [Countable E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {F : Finset E}
-- given
  (hA : DependsOn A (F : Set E)) :
-- imply
  A = MeasureTheory.cylinder F (ih_section A F) := by
-- proof
  apply StatMech.ih_eq_cylinder_of_dependsOn F hA

/--
[ih_harris_of_finite_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InfiniteHarris.lean)
-/
@[path]
private lemma ih_harris_of_finite_dependsOn_eq
  [Countable E]
  [DecidableEq E]
  {p : ℝ≥0}
  {A B : Set (ConfigSpace E)}
  {F : Finset E}
-- given
  (hp : p ≤ 1)
  (hAdep : DependsOn A (F : Set E))
  (hBdep : DependsOn B (F : Set E))
  (hAinc : IsIncreasing A)
  (hBinc : IsIncreasing B) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B ≤ (bernoulliProductMeasure (E := E) p hp).real (A ∩ B) := by
-- proof
  apply StatMech.ih_harris_of_finite_dependsOn hp F hAdep hBdep hAinc hBinc

/--
[ih_harris_iInter_of_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InfiniteHarris.lean)
-/
@[path]
private lemma ih_harris_iInter_of_antitone_eq
  [Countable E]
  [DecidableEq E]
  {mu : Measure (ConfigSpace E)}
  [IsProbabilityMeasure mu]
  {A B : ℕ → Set (ConfigSpace E)}
-- given
  (hAanti : Antitone A)
  (hBanti : Antitone B)
  (hAmeas : ∀ n, MeasurableSet (A n))
  (hBmeas : ∀ n, MeasurableSet (B n))
  (hstage : ∀ n, mu.real (A n) * mu.real (B n) ≤ mu.real (A n ∩ B n)) :
-- imply
  mu.real (⋂ n, A n) * mu.real (⋂ n, B n) ≤ mu.real ((⋂ n, A n) ∩ (⋂ n, B n)) := by
-- proof
  apply StatMech.ih_harris_iInter_of_antitone mu A B hAanti hBanti hAmeas hBmeas hstage

/--
[ih_tendsto_measureReal_iInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InfiniteHarris.lean)
-/
@[path]
private lemma ih_tendsto_measureReal_iInter_eq
  [Countable E]
  [DecidableEq E]
  [MeasurableSpace Ω]
  {mu : Measure Ω}
  [IsFiniteMeasure mu]
  {A : ℕ → Set Ω}
-- given
  (hanti : Antitone A)
  (hmeas : ∀ n, MeasurableSet (A n)) :
-- imply
  Tendsto (fun n => mu.real (A n)) atTop (nhds (mu.real (⋂ n, A n))) := by
-- proof
  apply StatMech.ih_tendsto_measureReal_iInter mu A hanti hmeas


-- created on 2026-10-23
