import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bfc2indep
open Set MeasureTheory ProbabilityTheory MeasurableSpace StatMech StatMech.Walls


/--
[bfc2_dependsOn_measurableSet_iSup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfc2indep.lean)
-/
@[path]
private lemma bfc2_dependsOn_measurableSet_iSup_eq
  {T : Set E}
  {B : Set (ConfigSpace E)}
-- given
  (hBmeas : MeasurableSet B)
  (hB : DependsOn B T) :
-- imply
  MeasurableSet[⨆ e ∈ T, MeasurableSpace.comap (fun ω : ConfigSpace E => ω e) inferInstance] B := by
-- proof
  apply StatMech.Walls.bfc2_dependsOn_measurableSet_iSup hBmeas hB

/--
[bfc2_indep_finite_cofinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfc2indep.lean)
-/
@[path]
private lemma bfc2_indep_finite_cofinite_eq
  {I : Finset E}
  {A B : Set (ConfigSpace E)}
-- given
  (p : NNReal)
  (hp : p ≤ 1)
  (hAmeas : MeasurableSet A)
  (hBmeas : MeasurableSet B)
  (hA : DependsOn A (↑I : Set E))
  (hB : DependsOn B (↑I : Set E)ᶜ) :
-- imply
  bernoulliProductMeasure (E := E) p hp (A ∩ B) = bernoulliProductMeasure (E := E) p hp A * bernoulliProductMeasure (E := E) p hp B := by
-- proof
  apply StatMech.Walls.bfc2_indep_finite_cofinite p hp I hAmeas hBmeas hA hB


-- created on 2026-10-23
