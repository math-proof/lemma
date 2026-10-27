import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.InclusionExclusion.Part4
open StatMech ConfigSpace StatMech.FK


/--
[one_mem_incrIndicators](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InclusionExclusion.lean)
-/
@[path]
private lemma one_mem_incrIndicators_eq :
-- imply
  (1 : ConfigSpace E → ℝ) ∈ incrIndicators E := by
-- proof
  apply StatMech.FK.one_mem_incrIndicators

/--
[openEvent_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InclusionExclusion.lean)
-/
@[path]
private lemma openEvent_increasing_eq
  {e : E} :
-- imply
  IsIncreasing {ω : ConfigSpace E | ω e = true} := by
-- proof
  apply StatMech.FK.openEvent_increasing e

/--
[openIndicator_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InclusionExclusion.lean)
-/
@[path]
private lemma openIndicator_mem_eq
  {e : E} :
-- imply
  ({ω : ConfigSpace E | ω e = true}).indicator (1 : ConfigSpace E → ℝ) ∈ incrIndicators E := by
-- proof
  apply StatMech.FK.openIndicator_mem e

/--
[signedIncreasingCombo_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InclusionExclusion.lean)
-/
@[path]
private lemma signedIncreasingCombo_iff_eq
  {f : ConfigSpace E → ℝ} :
-- imply
  SignedIncreasingCombo f ↔ ∃ (ι : Type) (s : Finset ι) (c : ι → ℝ) (A : ι → Set (ConfigSpace E)), (∀ i ∈ s, IsIncreasing (A i)) ∧ f = ∑ i ∈ s, c i • (A i).indicator (1 : ConfigSpace E → ℝ) := by
-- proof
  apply StatMech.FK.signedIncreasingCombo_iff f

/--
[span_mul_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InclusionExclusion.lean)
-/
@[path]
private lemma span_mul_mem_eq
  {f g : ConfigSpace E → ℝ}
-- given
  (hf : f ∈ Submodule.span ℝ (incrIndicators E))
  (hg : g ∈ Submodule.span ℝ (incrIndicators E)) :
-- imply
  f * g ∈ Submodule.span ℝ (incrIndicators E) := by
-- proof
  apply StatMech.FK.span_mul_mem hf hg

/--
[prod_mem_span](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InclusionExclusion.lean)
-/
@[path]
private lemma prod_mem_span_eq
  {s : Finset ι}
  {f : ι → ConfigSpace E → ℝ}
-- given
  (hf : ∀ i ∈ s, f i ∈ Submodule.span ℝ (incrIndicators E)) :
-- imply
  (∏ i ∈ s, f i) ∈ Submodule.span ℝ (incrIndicators E) := by
-- proof
  apply StatMech.FK.prod_mem_span s f hf

/--
[matcher_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InclusionExclusion.lean)
-/
@[path]
private lemma matcher_mem_eq
  {e : E}
  {b : Bool} :
-- imply
  (fun ω : ConfigSpace E => if ω e = b then (1 : ℝ) else 0) ∈ Submodule.span ℝ (incrIndicators E) := by
-- proof
  apply StatMech.FK.matcher_mem e b

/--
[cyl_indicator_eq_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InclusionExclusion.lean)
-/
@[path]
private lemma cyl_indicator_eq_prod_eq
  {S : Finset E}
  {ψ : ConfigSpace E} :
-- imply
  (cyl S ψ).indicator (1 : ConfigSpace E → ℝ) = ∏ e ∈ S, (fun ω : ConfigSpace E => if ω e = ψ e then (1 : ℝ) else 0) := by
-- proof
  apply StatMech.FK.cyl_indicator_eq_prod S ψ

/--
[cyl_indicator_signedIncreasingCombo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InclusionExclusion.lean)
-/
@[path]
private lemma cyl_indicator_signedIncreasingCombo_eq
  {S : Finset E}
  {ψ : ConfigSpace E} :
-- imply
  SignedIncreasingCombo ((cyl S ψ).indicator (1 : ConfigSpace E → ℝ)) := by
-- proof
  apply StatMech.FK.cyl_indicator_signedIncreasingCombo S ψ

/--
[repOf_agree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InclusionExclusion.lean)
-/
@[path]
private lemma repOf_agree_eq
  [DecidableEq E]
  {S : Finset E}
  {φ : ↥S → Bool}
  {e : E}
-- given
  (he : e ∈ S) :
-- imply
  repOf S φ e = φ ⟨e, he⟩ := by
-- proof
  apply StatMech.FK.repOf_agree S φ he

/--
[indicator_eq_sum_cyl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InclusionExclusion.lean)
-/
@[path]
private lemma indicator_eq_sum_cyl_eq
  [DecidableEq E]
  {C : Set (ConfigSpace E)}
  {S : Finset E}
-- given
  (hC : DependsOn (C.indicator (1 : ConfigSpace E → ℝ)) (S : Set E)) :
-- imply
  C.indicator (1 : ConfigSpace E → ℝ) = ∑ φ : ↥S → Bool, (C.indicator (1 : ConfigSpace E → ℝ) (repOf S φ)) • (cyl S (repOf S φ)).indicator 1 := by
-- proof
  apply StatMech.FK.indicator_eq_sum_cyl C S hC

/--
[indicator_signedIncreasingCombo_of_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InclusionExclusion.lean)
-/
@[path]
private lemma indicator_signedIncreasingCombo_of_dependsOn_eq
  [DecidableEq E]
  {C : Set (ConfigSpace E)}
  {S : Finset E}
-- given
  (hC : DependsOn (C.indicator (1 : ConfigSpace E → ℝ)) (S : Set E)) :
-- imply
  SignedIncreasingCombo (C.indicator (1 : ConfigSpace E → ℝ)) := by
-- proof
  apply StatMech.FK.indicator_signedIncreasingCombo_of_dependsOn C S hC


-- created on 2026-10-23
