import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarAspectOrientationNoGo.Part2
open MeasureTheory Set StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[isFKG_dirac](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarAspectOrientationNoGo.lean)
-/
@[path]
private lemma isFKG_dirac_eq
  {V : Type}
  {omega : ConfigSpace (Sym2 V)} :
-- imply
  IsFKG (Measure.dirac omega) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.isFKG_dirac omega

/--
[aspectOrientationCertainEvent_measurable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarAspectOrientationNoGo.lean)
-/
@[path]
private lemma aspectOrientationCertainEvent_measurable_eq :
-- imply
  MeasurableSet aspectOrientationCertainEvent := by
-- proof
  apply StatMech.FK.PeriodicPlanar.aspectOrientationCertainEvent_measurable

/--
[aspectOrientationAbsentEvent_measurable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarAspectOrientationNoGo.lean)
-/
@[path]
private lemma aspectOrientationAbsentEvent_measurable_eq :
-- imply
  MeasurableSet aspectOrientationAbsentEvent := by
-- proof
  apply StatMech.FK.PeriodicPlanar.aspectOrientationAbsentEvent_measurable

/--
[aspectOrientationCertainEvent_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarAspectOrientationNoGo.lean)
-/
@[path]
private lemma aspectOrientationCertainEvent_increasing_eq :
-- imply
  IsIncreasing aspectOrientationCertainEvent := by
-- proof
  apply StatMech.FK.PeriodicPlanar.aspectOrientationCertainEvent_increasing

/--
[aspectOrientationAbsentEvent_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarAspectOrientationNoGo.lean)
-/
@[path]
private lemma aspectOrientationAbsentEvent_increasing_eq :
-- imply
  IsIncreasing aspectOrientationAbsentEvent := by
-- proof
  apply StatMech.FK.PeriodicPlanar.aspectOrientationAbsentEvent_increasing

/--
[aspectOrientationCounterexample_isFKG](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarAspectOrientationNoGo.lean)
-/
@[path]
private lemma aspectOrientationCounterexample_isFKG_eq :
-- imply
  IsFKG (Measure.dirac aspectOrientationCounterexampleConfig) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.aspectOrientationCounterexample_isFKG

/--
[aspectOrientationCertainEvent_measureReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarAspectOrientationNoGo.lean)
-/
@[path]
private lemma aspectOrientationCertainEvent_measureReal_eq :
-- imply
  (Measure.dirac aspectOrientationCounterexampleConfig).real aspectOrientationCertainEvent = 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.aspectOrientationCertainEvent_measureReal

/--
[aspectOrientationAbsentEvent_measureReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarAspectOrientationNoGo.lean)
-/
@[path]
private lemma aspectOrientationAbsentEvent_measureReal_eq :
-- imply
  (Measure.dirac aspectOrientationCounterexampleConfig).real aspectOrientationAbsentEvent = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.aspectOrientationAbsentEvent_measureReal

/--
[not_fkg_implies_increasing_event_orientation_comparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarAspectOrientationNoGo.lean)
-/
@[path]
private lemma not_fkg_implies_increasing_event_orientation_comparison_eq :
-- imply
  ¬ (∀ (mu : Measure (ConfigSpace (Sym2 (Fin 2)))), IsFKG mu → ∀ A B : Set (ConfigSpace (Sym2 (Fin 2))), MeasurableSet A → MeasurableSet B → IsIncreasing A → IsIncreasing B → mu.real A ≤ mu.real B) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.not_fkg_implies_increasing_event_orientation_comparison


-- created on 2026-10-23
