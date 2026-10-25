import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc_steplocal
open SimpleGraph StatMech StatMech.Walls


/--
[jc_headTravel_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_steplocal.lean)
-/
@[path]
private lemma jc_headTravel_eq_eq
  {e : Dart} :
-- imply
  jc_headTravel e = e.head + (-rot90Fun e.dir) := by
-- proof
  apply StatMech.Walls.jc_headTravel_eq e

/--
[jc_tailTravel_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_steplocal.lean)
-/
@[path]
private lemma jc_tailTravel_eq_eq
  {e : Dart} :
-- imply
  jc_tailTravel e = e.tail + (-rot90Fun e.dir) := by
-- proof
  apply StatMech.Walls.jc_tailTravel_eq e

/--
[jc_dartNext_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_steplocal.lean)
-/
@[path]
private lemma jc_dartNext_congr_eq
  {K K' : Set (Site 2)}
  {e : Dart}
-- given
  (hhead : jc_headTravel e ∈ K ↔ jc_headTravel e ∈ K')
  (htail : jc_tailTravel e ∈ K ↔ jc_tailTravel e ∈ K') :
-- imply
  dartNext K e = dartNext K' e := by
-- proof
  apply StatMech.Walls.jc_dartNext_congr K K' e hhead htail

/--
[jc_turnZ_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_steplocal.lean)
-/
@[path]
private lemma jc_turnZ_congr_eq
  {K K' : Set (Site 2)}
  {e : Dart}
-- given
  (hhead : jc_headTravel e ∈ K ↔ jc_headTravel e ∈ K')
  (htail : jc_tailTravel e ∈ K ↔ jc_tailTravel e ∈ K') :
-- imply
  turnZ K e = turnZ K' e := by
-- proof
  apply StatMech.Walls.jc_turnZ_congr K K' e hhead htail

/--
[jc_turn_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_steplocal.lean)
-/
@[path]
private lemma jc_turn_congr_eq
  {K K' : Set (Site 2)}
  {e : Dart}
-- given
  (hhead : jc_headTravel e ∈ K ↔ jc_headTravel e ∈ K')
  (htail : jc_tailTravel e ∈ K ↔ jc_tailTravel e ∈ K') :
-- imply
  turn K e = turn K' e := by
-- proof
  apply StatMech.Walls.jc_turn_congr K K' e hhead htail

/--
[jc_step_local](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_steplocal.lean)
-/
@[path]
private lemma jc_step_local_eq
  {K K' : Set (Site 2)}
  {e : Dart}
-- given
  (hhead : jc_headTravel e ∈ K ↔ jc_headTravel e ∈ K')
  (htail : jc_tailTravel e ∈ K ↔ jc_tailTravel e ∈ K') :
-- imply
  dartNext K e = dartNext K' e ∧ turnZ K e = turnZ K' e ∧ turn K e = turn K' e := by
-- proof
  apply StatMech.Walls.jc_step_local K K' e hhead htail

/--
[jc_step_local_of_agree_on_probes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_steplocal.lean)
-/
@[path]
private lemma jc_step_local_of_agree_on_probes_eq
  {K K' : Set (Site 2)}
  {e : Dart}
-- given
  (hagree : ∀ x, (x = jc_headTravel e ∨ x = jc_tailTravel e) → (x ∈ K ↔ x ∈ K')) :
-- imply
  dartNext K e = dartNext K' e ∧ turnZ K e = turnZ K' e ∧ turn K e = turn K' e := by
-- proof
  apply StatMech.Walls.jc_step_local_of_agree_on_probes K K' e hagree

/--
[jc_step_local_of_symmDiff_avoids](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc_steplocal.lean)
-/
@[path]
private lemma jc_step_local_of_symmDiff_avoids_eq
  {K K' : Set (Site 2)}
  {e : Dart}
-- given
  (hhead : jc_headTravel e ∉ (K \ K') ∪ (K' \ K))
  (htail : jc_tailTravel e ∉ (K \ K') ∪ (K' \ K)) :
-- imply
  dartNext K e = dartNext K' e ∧ turnZ K e = turnZ K' e ∧ turn K e = turn K' e := by
-- proof
  apply StatMech.Walls.jc_step_local_of_symmDiff_avoids K K' e hhead htail


-- created on 2026-10-23
