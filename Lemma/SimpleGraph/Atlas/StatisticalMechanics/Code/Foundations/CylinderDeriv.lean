import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Foundations.CylinderDeriv.Part2
open MeasureTheory ProbabilityTheory Function StatMech


/--
[bernoulliMeasure_real_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CylinderDeriv.lean)
-/
@[path]
private lemma bernoulliMeasure_real_singleton_eq
  [Countable E]
  [DecidableEq E]
  {b : Bool}
-- given
  (p : NNReal)
  (hp : p ≤ 1) :
-- imply
  (bernoulliMeasure p hp).real {b} = if b then (p : ℝ) else 1 - p := by
-- proof
  apply StatMech.bernoulliMeasure_real_singleton p hp b

/--
[realSingleton_eq_configWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CylinderDeriv.lean)
-/
@[path]
private lemma realSingleton_eq_configWeight_eq
  [Countable E]
  [DecidableEq E]
  [Fintype E]
  {ω : ConfigSpace E}
-- given
  (p : NNReal)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real {ω} = configWeight (p : ℝ) ω := by
-- proof
  apply StatMech.realSingleton_eq_configWeight p hp ω

/--
[finiteRealProb_eq_prob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CylinderDeriv.lean)
-/
@[path]
private lemma finiteRealProb_eq_prob_eq
  [Countable E]
  [DecidableEq E]
  [Fintype E]
  {S : Set (ConfigSpace E)}
-- given
  (p : NNReal)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real S = prob (p : ℝ) S := by
-- proof
  apply StatMech.finiteRealProb_eq_prob p hp S

/--
[restrict_extendOff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CylinderDeriv.lean)
-/
@[path]
private lemma restrict_extendOff_eq
  [Countable E]
  [DecidableEq E]
  {F : Finset E}
  {ω : ConfigSpace E}
  {η : ConfigSpace ↥F} :
-- imply
  F.restrict (extendOff F ω η) = η := by
-- proof
  apply StatMech.restrict_extendOff F ω η

/--
[eq_cylinder_restrict_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CylinderDeriv.lean)
-/
@[path]
private lemma eq_cylinder_restrict_image_eq
  [Countable E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {F : Finset E}
-- given
  (hA : DependsOn (A.indicator (fun _ => (1 : ℝ))) (F : Set E)) :
-- imply
  A = cylinder F (F.restrict '' A) := by
-- proof
  apply StatMech.eq_cylinder_restrict_image A F hA

/--
[bernoulliProductMeasure_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CylinderDeriv.lean)
-/
@[path]
private lemma bernoulliProductMeasure_cylinder_eq
  [Countable E]
  [DecidableEq E]
  {F : Finset E}
  {S : Set (ConfigSpace ↥F)}
-- given
  (p : NNReal)
  (hp : p ≤ 1) :
-- imply
  bernoulliProductMeasure (E := E) p hp (cylinder F S) = bernoulliProductMeasure (E := ↥F) p hp S := by
-- proof
  apply StatMech.bernoulliProductMeasure_cylinder p hp F S

/--
[realProb_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CylinderDeriv.lean)
-/
@[path]
private lemma realProb_cylinder_eq
  [Countable E]
  [DecidableEq E]
  {F : Finset E}
  {S : Set (ConfigSpace ↥F)}
-- given
  (p : NNReal)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (cylinder F S) = (bernoulliProductMeasure (E := ↥F) p hp).real S := by
-- proof
  apply StatMech.realProb_cylinder p hp F S

/--
[realProb_cylinder_eq_prob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CylinderDeriv.lean)
-/
@[path]
private lemma realProb_cylinder_eq_prob_eq
  [Countable E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {F : Finset E}
-- given
  (p : NNReal)
  (hp : p ≤ 1)
  (hA : DependsOn (A.indicator (fun _ => (1 : ℝ))) (F : Set E)) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real A = prob (p : ℝ) (F.restrict '' A) := by
-- proof
  apply StatMech.realProb_cylinder_eq_prob p hp A F hA

/--
[realProb_cylinder_eq_finsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CylinderDeriv.lean)
-/
@[path]
private lemma realProb_cylinder_eq_finsum_eq
  [Countable E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {F : Finset E}
-- given
  (p : NNReal)
  (hp : p ≤ 1)
  (hA : DependsOn (A.indicator (fun _ => (1 : ℝ))) (F : Set E)) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real A = ∑ η : ConfigSpace ↥F, (F.restrict '' A).indicator (fun _ => (1 : ℝ)) η * ∏ e : ↥F, (if η e then (p : ℝ) else 1 - p) := by
-- proof
  apply StatMech.realProb_cylinder_eq_finsum p hp A F hA

/--
[hasDerivAt_realProb_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CylinderDeriv.lean)
-/
@[path]
private lemma hasDerivAt_realProb_cylinder_eq
  [Countable E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {F : Finset E}
  {q : ℝ} :
-- imply
  HasDerivAt (fun q => prob q (F.restrict '' A)) (∑ ω : ConfigSpace ↥F, (F.restrict '' A).indicator (fun _ => (1 : ℝ)) ω * ∑ e : ↥F, weightOff q e ω * (if ω e then (1 : ℝ) else -1)) q := by
-- proof
  apply StatMech.hasDerivAt_realProb_cylinder A F q

/--
[differentiable_realProb_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CylinderDeriv.lean)
-/
@[path]
private lemma differentiable_realProb_cylinder_eq
  [Countable E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {F : Finset E} :
-- imply
  Differentiable ℝ (fun q => prob q (F.restrict '' A)) := by
-- proof
  apply StatMech.differentiable_realProb_cylinder A F

/--
[isIncreasing_restrict_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CylinderDeriv.lean)
-/
@[path]
private lemma isIncreasing_restrict_image_eq
  [Countable E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {F : Finset E}
-- given
  (hA : IsIncreasing A) :
-- imply
  IsIncreasing (F.restrict '' A) := by
-- proof
  apply StatMech.isIncreasing_restrict_image A hA F

/--
[hasDerivAt_realProb_cylinder_pivotal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CylinderDeriv.lean)
-/
@[path]
private lemma hasDerivAt_realProb_cylinder_pivotal_eq
  [Countable E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {F : Finset E}
  {q : ℝ}
-- given
  (hA : IsIncreasing A) :
-- imply
  HasDerivAt (fun q => prob q (F.restrict '' A)) (∑ e : ↥F, pivotalProb q (F.restrict '' A) e) q := by
-- proof
  apply StatMech.hasDerivAt_realProb_cylinder_pivotal A hA F q

/--
[deriv_realProb_cylinder_pivotal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CylinderDeriv.lean)
-/
@[path]
private lemma deriv_realProb_cylinder_pivotal_eq
  [Countable E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
  {F : Finset E}
  {q : ℝ}
-- given
  (hA : IsIncreasing A) :
-- imply
  deriv (fun q => prob q (F.restrict '' A)) q = ∑ e : ↥F, pivotalProb q (F.restrict '' A) e := by
-- proof
  apply StatMech.deriv_realProb_cylinder_pivotal A hA F q


-- created on 2026-10-23
