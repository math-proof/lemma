import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.CobhamBaseDependence
open MetaMathlibExt


/--
[cobham_base_dependence](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CobhamBaseDependence.lean)
-/
@[path]
private lemma cobham_base_dependence_eq
  {k l : ℕ}
  {S : Set ℕ}
-- given
  (hl : 2 ≤ l)
  (hindependent : BasesMultiplicativelyIndependent k l)
  (hrecognizable : IsBaseRecognizable k S)
  (haperiodic : ¬ IsUltimatelyPeriodicSet S) :
-- imply
  ¬ IsBaseRecognizable l S := by
-- proof
  apply MetaMathlibExt.cobham_base_dependence hl hindependent hrecognizable haperiodic

/--
[isUltimatelyPeriodicSet_iff_isUltimatelyPeriodic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CobhamBaseDependence.lean)
-/
@[path]
private lemma isUltimatelyPeriodicSet_iff_isUltimatelyPeriodic_eq
  {S : Set ℕ} :
-- imply
  IsUltimatelyPeriodicSet S ↔ IsUltimatelyPeriodic (fun n => n ∈ S) := by
-- proof
  apply MetaMathlibExt.isUltimatelyPeriodicSet_iff_isUltimatelyPeriodic S

/--
[cobham_base_dependence_isUltimatelyPeriodic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CobhamBaseDependence.lean)
-/
@[path]
private lemma cobham_base_dependence_isUltimatelyPeriodic_eq
  {k l : ℕ}
  {S : Set ℕ}
-- given
  (hl : 2 ≤ l)
  (hindependent : BasesMultiplicativelyIndependent k l)
  (hrecognizable : IsBaseRecognizable k S)
  (haperiodic : ¬ IsUltimatelyPeriodic (fun n => n ∈ S)) :
-- imply
  ¬ IsBaseRecognizable l S := by
-- proof
  apply MetaMathlibExt.cobham_base_dependence_isUltimatelyPeriodic hl hindependent hrecognizable haperiodic


-- created on 2026-10-20
