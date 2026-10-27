import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Probability.InfiniteBK
open MeasureTheory Set StatMech


/--
[ibk_occursOn_mono_config](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InfiniteBK.lean)
-/
@[path]
private lemma ibk_occursOn_mono_config_eq
  [Countable E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {K : Set E}
  {omega omega' : ConfigSpace E}
-- given
  (hA : IsIncreasing A)
  (homega : omega ≤ omega')
  (hocc : OccursOn A K omega) :
-- imply
  OccursOn A K omega' := by
-- proof
  apply StatMech.ibk_occursOn_mono_config hA homega hocc

/--
[ibk_disjointOccurrence_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InfiniteBK.lean)
-/
@[path]
private lemma ibk_disjointOccurrence_isIncreasing_eq
  [Countable E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
-- given
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  IsIncreasing (disjointOccurrence A B) := by
-- proof
  apply StatMech.ibk_disjointOccurrence_isIncreasing hA hB

/--
[ibk_occursOn_inter_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InfiniteBK.lean)
-/
@[path]
private lemma ibk_occursOn_inter_finite_eq
  [Countable E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {F : Finset E}
  {K : Set E}
  {omega omega' : ConfigSpace E}
-- given
  (hA : DependsOn A (F : Set E))
  (hocc : OccursOn A K omega)
  (hagree : agreeOn (F : Set E) omega omega') :
-- imply
  OccursOn A (K ∩ (F : Set E)) omega' := by
-- proof
  apply StatMech.ibk_occursOn_inter_finite hA hocc hagree

/--
[ibk_disjointOccurrence_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InfiniteBK.lean)
-/
@[path]
private lemma ibk_disjointOccurrence_dependsOn_eq
  [Countable E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {F : Finset E}
-- given
  (hA : DependsOn A (F : Set E))
  (hB : DependsOn B (F : Set E)) :
-- imply
  DependsOn (disjointOccurrence A B) (F : Set E) := by
-- proof
  apply StatMech.ibk_disjointOccurrence_dependsOn hA hB

/--
[ibk_section_disjointOccurrence_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InfiniteBK.lean)
-/
@[path]
private lemma ibk_section_disjointOccurrence_subset_eq
  [Countable E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {F : Finset E} :
-- imply
  ih_section (disjointOccurrence A B) F ⊆ disjointOccurrence (ih_section A F) (ih_section B F) := by
-- proof
  apply StatMech.ibk_section_disjointOccurrence_subset A B F

/--
[ibk_inequality_of_finite_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InfiniteBK.lean)
-/
@[path]
private lemma ibk_inequality_of_finite_dependsOn_eq
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
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.ibk_inequality_of_finite_dependsOn hp F hAdep hBdep hAinc hBinc

/--
[ibk_triple_of_finite_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InfiniteBK.lean)
-/
@[path]
private lemma ibk_triple_of_finite_dependsOn_eq
  [Countable E]
  [DecidableEq E]
  {p : ℝ≥0}
  {P Q R : Set (ConfigSpace E)}
  {F : Finset E}
-- given
  (hp : p ≤ 1)
  (hPdep : DependsOn P (F : Set E))
  (hQdep : DependsOn Q (F : Set E))
  (hRdep : DependsOn R (F : Set E))
  (hP : IsIncreasing P)
  (hQ : IsIncreasing Q)
  (hR : IsIncreasing R) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence P (disjointOccurrence Q R)) ≤ (bernoulliProductMeasure (E := E) p hp).real P * (bernoulliProductMeasure (E := E) p hp).real Q * (bernoulliProductMeasure (E := E) p hp).real R := by
-- proof
  apply StatMech.ibk_triple_of_finite_dependsOn hp F hPdep hQdep hRdep hP hQ hR

/--
[ibk_criterion_of_finite_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InfiniteBK.lean)
-/
@[path]
private lemma ibk_criterion_of_finite_dependsOn_eq
  [Countable E]
  [DecidableEq E]
  {p : ℝ≥0}
  {s : Finset I}
  {P Q R : I → Set (ConfigSpace E)}
  {F : Finset E}
  {C : Set (ConfigSpace E)}
-- given
  (hp : p ≤ 1)
  (hPdep : ∀ i ∈ s, DependsOn (P i) (F : Set E))
  (hQdep : ∀ i ∈ s, DependsOn (Q i) (F : Set E))
  (hRdep : ∀ i ∈ s, DependsOn (R i) (F : Set E))
  (hP : ∀ i ∈ s, IsIncreasing (P i))
  (hQ : ∀ i ∈ s, IsIncreasing (Q i))
  (hR : ∀ i ∈ s, IsIncreasing (R i))
  (hC : C ⊆ ⋃ i ∈ s, disjointOccurrence (P i) (disjointOccurrence (Q i) (R i))) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real C ≤ ∑ i ∈ s, (bernoulliProductMeasure (E := E) p hp).real (P i) * (bernoulliProductMeasure (E := E) p hp).real (Q i) * (bernoulliProductMeasure (E := E) p hp).real (R i) := by
-- proof
  apply StatMech.ibk_criterion_of_finite_dependsOn hp s P Q R F hPdep hQdep hRdep hP hQ hR hC

/--
[ibk_configWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InfiniteBK.lean)
-/
@[path]
private lemma ibk_configWeight_nonneg_eq
  [Countable E]
  [DecidableEq E]
  [Fintype E]
  {r : ℝ}
  {omega : ConfigSpace E}
-- given
  (hr0 : 0 ≤ r)
  (hr1 : r ≤ 1) :
-- imply
  0 ≤ configWeight r omega := by
-- proof
  apply StatMech.ibk_configWeight_nonneg hr0 hr1 omega

/--
[ibk_pivotalProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InfiniteBK.lean)
-/
@[path]
private lemma ibk_pivotalProb_nonneg_eq
  [Countable E]
  [DecidableEq E]
  [Fintype E]
  {r : ℝ}
  {A : Set (ConfigSpace E)}
  {e : E}
-- given
  (hr0 : 0 ≤ r)
  (hr1 : r ≤ 1) :
-- imply
  0 ≤ pivotalProb r A e := by
-- proof
  apply StatMech.ibk_pivotalProb_nonneg hr0 hr1 A e

/--
[ibk_measure_mono_parameter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InfiniteBK.lean)
-/
@[path]
private lemma ibk_measure_mono_parameter_eq
  [Countable E]
  [DecidableEq E]
  {p q : ℝ≥0}
  {A : Set (ConfigSpace E)}
  {F : Finset E}
-- given
  (hp : p ≤ 1)
  (hq : q ≤ 1)
  (hpq : p ≤ q)
  (hAdep : DependsOn A (F : Set E))
  (hAinc : IsIncreasing A) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real A ≤ (bernoulliProductMeasure (E := E) q hq).real A := by
-- proof
  apply StatMech.ibk_measure_mono_parameter hp hq hpq F hAdep hAinc


-- created on 2026-10-23
