import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc3_earfootprint.Part3
open SimpleGraph Function StatMech StatMech.Walls


/--
[jc3_mem_earFootprint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_earfootprint.lean)
-/
@[path]
private lemma jc3_mem_earFootprint_eq
  {r x : Site 2} :
-- imply
  x ∈ jc3_earFootprint r ↔ x = r ∨ x = r + ![1, 0] ∨ x = r + ![(-1 : ℤ), 0] ∨ x = r + ![0, 1] ∨ x = r + ![0, (-1 : ℤ)] := by
-- proof
  apply StatMech.Walls.jc3_mem_earFootprint r x

/--
[jc3_self_mem_earFootprint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_earfootprint.lean)
-/
@[path]
private lemma jc3_self_mem_earFootprint_eq
  {r : Site 2} :
-- imply
  r ∈ jc3_earFootprint r := by
-- proof
  apply StatMech.Walls.jc3_self_mem_earFootprint r

/--
[jc3_right_mem_earFootprint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_earfootprint.lean)
-/
@[path]
private lemma jc3_right_mem_earFootprint_eq
  {r : Site 2} :
-- imply
  r + ![1, 0] ∈ jc3_earFootprint r := by
-- proof
  apply StatMech.Walls.jc3_right_mem_earFootprint r

/--
[jc3_left_mem_earFootprint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_earfootprint.lean)
-/
@[path]
private lemma jc3_left_mem_earFootprint_eq
  {r : Site 2} :
-- imply
  r + ![(-1 : ℤ), 0] ∈ jc3_earFootprint r := by
-- proof
  apply StatMech.Walls.jc3_left_mem_earFootprint r

/--
[jc3_up_mem_earFootprint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_earfootprint.lean)
-/
@[path]
private lemma jc3_up_mem_earFootprint_eq
  {r : Site 2} :
-- imply
  r + ![0, 1] ∈ jc3_earFootprint r := by
-- proof
  apply StatMech.Walls.jc3_up_mem_earFootprint r

/--
[jc3_down_mem_earFootprint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_earfootprint.lean)
-/
@[path]
private lemma jc3_down_mem_earFootprint_eq
  {r : Site 2} :
-- imply
  r + ![0, (-1 : ℤ)] ∈ jc3_earFootprint r := by
-- proof
  apply StatMech.Walls.jc3_down_mem_earFootprint r

/--
[jc3_earFootprint_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_earfootprint.lean)
-/
@[path]
private lemma jc3_earFootprint_finite_eq
  {r : Site 2} :
-- imply
  (jc3_earFootprint r).Finite := by
-- proof
  apply StatMech.Walls.jc3_earFootprint_finite r

/--
[jc3_notProbed_of_avoidsEarFootprint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_earfootprint.lean)
-/
@[path]
private lemma jc3_notProbed_of_avoidsEarFootprint_eq
  {r : Site 2}
  {e : Dart}
-- given
  (h : jc3_AvoidsEarFootprint r e) :
-- imply
  bpc_NotProbed r e := by
-- proof
  apply StatMech.Walls.jc3_notProbed_of_avoidsEarFootprint r e h

/--
[jc3_dartNext_eq_of_avoidsEarFootprint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_earfootprint.lean)
-/
@[path]
private lemma jc3_dartNext_eq_of_avoidsEarFootprint_eq
  {K : Set (Site 2)}
  {r : Site 2}
  {e : Dart}
-- given
  (h : jc3_AvoidsEarFootprint r e) :
-- imply
  dartNext (K \ {r}) e = dartNext K e := by
-- proof
  apply StatMech.Walls.jc3_dartNext_eq_of_avoidsEarFootprint K r e h

/--
[jc3_turnZ_eq_of_avoidsEarFootprint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_earfootprint.lean)
-/
@[path]
private lemma jc3_turnZ_eq_of_avoidsEarFootprint_eq
  {K : Set (Site 2)}
  {r : Site 2}
  {e : Dart}
-- given
  (h : jc3_AvoidsEarFootprint r e) :
-- imply
  turnZ (K \ {r}) e = turnZ K e := by
-- proof
  apply StatMech.Walls.jc3_turnZ_eq_of_avoidsEarFootprint K r e h

/--
[jc3_step_eq_of_avoidsEarFootprint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_earfootprint.lean)
-/
@[path]
private lemma jc3_step_eq_of_avoidsEarFootprint_eq
  {K : Set (Site 2)}
  {r : Site 2}
  {e : Dart}
-- given
  (h : jc3_AvoidsEarFootprint r e) :
-- imply
  dartNext (K \ {r}) e = dartNext K e ∧ turnZ (K \ {r}) e = turnZ K e := by
-- proof
  apply StatMech.Walls.jc3_step_eq_of_avoidsEarFootprint K r e h

/--
[jc3_earFootprintLocality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_earfootprint.lean)
-/
@[path]
private lemma jc3_earFootprintLocality_eq
  {K : Set (Site 2)}
  {r : Site 2}
  {e : Dart}
-- given
  (h : jc3_AvoidsEarFootprint r e) :
-- imply
  dartNext (K \ {r}) e = dartNext K e ∧ turnZ (K \ {r}) e = turnZ K e ∧ turn (K \ {r}) e = turn K e := by
-- proof
  apply StatMech.Walls.jc3_earFootprintLocality K r e h

/--
[jc3_mem_diff_singleton_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_earfootprint.lean)
-/
@[path]
private lemma jc3_mem_diff_singleton_of_ne_eq
  {K : Set (Site 2)}
  {r x : Site 2}
-- given
  (hx : x ≠ r) :
-- imply
  x ∈ K \ {r} ↔ x ∈ K := by
-- proof
  apply StatMech.Walls.jc3_mem_diff_singleton_of_ne K r x hx

/--
[jc3_symmDiff_diff_singleton_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_earfootprint.lean)
-/
@[path]
private lemma jc3_symmDiff_diff_singleton_subset_eq
  {K : Set (Site 2)}
  {r : Site 2} :
-- imply
  (K \ (K \ {r})) ∪ ((K \ {r}) \ K) ⊆ {r} := by
-- proof
  apply StatMech.Walls.jc3_symmDiff_diff_singleton_subset K r

/--
[jc3_farDart_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_earfootprint.lean)
-/
@[path]
private lemma jc3_farDart_dir_eq :
-- imply
  jc3_farDart.dir = ![1, 0] := by
-- proof
  apply StatMech.Walls.jc3_farDart_dir

/--
[jc3_farDart_avoidsOrigin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_earfootprint.lean)
-/
@[path]
private lemma jc3_farDart_avoidsOrigin_eq :
-- imply
  jc3_AvoidsEarFootprint (![0, 0] : Site 2) jc3_farDart := by
-- proof
  apply StatMech.Walls.jc3_farDart_avoidsOrigin

/--
[jc3_farDart_step_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_earfootprint.lean)
-/
@[path]
private lemma jc3_farDart_step_eq_eq
  {K : Set (Site 2)} :
-- imply
  dartNext (K \ {(![0, 0] : Site 2)}) jc3_farDart = dartNext K jc3_farDart ∧ turnZ (K \ {(![0, 0] : Site 2)}) jc3_farDart = turnZ K jc3_farDart := by
-- proof
  apply StatMech.Walls.jc3_farDart_step_eq K


-- created on 2026-10-23
