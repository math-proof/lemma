import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
open MeasureTheory TopologicalSpace StatMech StatMech.ConfigSpace


/--
[eval_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ConfigSpace.lean)
-/
@[path]
private lemma eval_apply_eq
  {e : E}
  {ω : ConfigSpace E} :
-- imply
  eval e ω = ω e := by
-- proof
  apply StatMech.ConfigSpace.eval_apply e ω

/--
[continuous_eval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ConfigSpace.lean)
-/
@[path]
private lemma continuous_eval_eq
  {e : E} :
-- imply
  Continuous (eval e) := by
-- proof
  apply StatMech.ConfigSpace.continuous_eval e

/--
[measurable_eval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ConfigSpace.lean)
-/
@[path]
private lemma measurable_eval_eq
  {e : E} :
-- imply
  Measurable (eval e) := by
-- proof
  apply StatMech.ConfigSpace.measurable_eval e

/--
[measurableSpace_eq_iSup_comap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ConfigSpace.lean)
-/
@[path]
private lemma measurableSpace_eq_iSup_comap_eq :
-- imply
  (inferInstance : MeasurableSpace (ConfigSpace E)) = ⨆ e, MeasurableSpace.comap (eval e) inferInstance := by
-- proof
  apply StatMech.ConfigSpace.measurableSpace_eq_iSup_comap

/--
[isCompact_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ConfigSpace.lean)
-/
@[path]
private lemma isCompact_univ_eq :
-- imply
  IsCompact (Set.univ : Set (ConfigSpace E)) := by
-- proof
  apply StatMech.ConfigSpace.isCompact_univ

/--
[t2Space](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ConfigSpace.lean)
-/
@[path]
private lemma t2Space_eq :
-- imply
  T2Space (ConfigSpace E) := by
-- proof
  apply StatMech.ConfigSpace.t2Space

/--
[metrizableSpace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ConfigSpace.lean)
-/
@[path]
private lemma metrizableSpace_eq
  [Countable E] :
-- imply
  MetrizableSpace (ConfigSpace E) := by
-- proof
  apply StatMech.ConfigSpace.metrizableSpace

/--
[secondCountableTopology](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/ConfigSpace.lean)
-/
@[path]
private lemma secondCountableTopology_eq
  [Countable E] :
-- imply
  SecondCountableTopology (ConfigSpace E) := by
-- proof
  apply StatMech.ConfigSpace.secondCountableTopology


-- created on 2026-10-23
