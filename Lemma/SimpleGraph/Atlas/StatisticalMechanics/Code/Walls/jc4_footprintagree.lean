import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc4_footprintagree
open SimpleGraph Function StatMech StatMech.Walls


/--
[jc4_notProbed_of_avoidsEarFootprint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_footprintagree.lean)
-/
@[path]
private lemma jc4_notProbed_of_avoidsEarFootprint_eq
  {r : Site 2}
  {e : Dart}
-- given
  (h : jc3_AvoidsEarFootprint r e) :
-- imply
  bpc_NotProbed r e := by
-- proof
  apply StatMech.Walls.jc4_notProbed_of_avoidsEarFootprint r e h

/--
[jc4_dartNext_eq_of_avoidsEarFootprint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_footprintagree.lean)
-/
@[path]
private lemma jc4_dartNext_eq_of_avoidsEarFootprint_eq
  {K : Set (Site 2)}
  {r : Site 2}
  {e : Dart}
-- given
  (h : jc3_AvoidsEarFootprint r e) :
-- imply
  dartNext (K \ {r}) e = dartNext K e := by
-- proof
  apply StatMech.Walls.jc4_dartNext_eq_of_avoidsEarFootprint K r e h

/--
[jc4_turnZ_eq_of_avoidsEarFootprint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_footprintagree.lean)
-/
@[path]
private lemma jc4_turnZ_eq_of_avoidsEarFootprint_eq
  {K : Set (Site 2)}
  {r : Site 2}
  {e : Dart}
-- given
  (h : jc3_AvoidsEarFootprint r e) :
-- imply
  turnZ (K \ {r}) e = turnZ K e := by
-- proof
  apply StatMech.Walls.jc4_turnZ_eq_of_avoidsEarFootprint K r e h

/--
[jc4_footprintAgree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_footprintagree.lean)
-/
@[path]
private lemma jc4_footprintAgree_eq
  {K : Set (Site 2)}
  {r : Site 2}
  {e : Dart}
-- given
  (h : jc3_AvoidsEarFootprint r e) :
-- imply
  bpc_NotProbed r e ∧ dartNext (K \ {r}) e = dartNext K e ∧ turnZ (K \ {r}) e = turnZ K e := by
-- proof
  apply StatMech.Walls.jc4_footprintAgree K r e h

/--
[jc4_footprintAgree_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_footprintagree.lean)
-/
@[path]
private lemma jc4_footprintAgree_full_eq
  {K : Set (Site 2)}
  {r : Site 2}
  {e : Dart}
-- given
  (h : jc3_AvoidsEarFootprint r e) :
-- imply
  bpc_NotProbed r e ∧ dartNext (K \ {r}) e = dartNext K e ∧ turnZ (K \ {r}) e = turnZ K e ∧ turn (K \ {r}) e = turn K e := by
-- proof
  apply StatMech.Walls.jc4_footprintAgree_full K r e h

/--
[jc4_footprintAgree_orbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_footprintagree.lean)
-/
@[path]
private lemma jc4_footprintAgree_orbit_eq
  {K : Set (Site 2)}
  {r : Site 2}
  {e : Dart}
  {i : ℕ}
-- given
  (hfoot : ∀ i, jc3_AvoidsEarFootprint r ((dartNext K)^[i] e)) :
-- imply
  bpc_NotProbed r ((dartNext K)^[i] e) ∧ dartNext (K \ {r}) ((dartNext K)^[i] e) = dartNext K ((dartNext K)^[i] e) ∧ turnZ (K \ {r}) ((dartNext K)^[i] e) = turnZ K ((dartNext K)^[i] e) := by
-- proof
  apply StatMech.Walls.jc4_footprintAgree_orbit K r e hfoot i

/--
[jc4_farDart_footprintAgree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_footprintagree.lean)
-/
@[path]
private lemma jc4_farDart_footprintAgree_eq
  {K : Set (Site 2)} :
-- imply
  bpc_NotProbed (![0, 0] : Site 2) jc3_farDart ∧ dartNext (K \ {(![0, 0] : Site 2)}) jc3_farDart = dartNext K jc3_farDart ∧ turnZ (K \ {(![0, 0] : Site 2)}) jc3_farDart = turnZ K jc3_farDart := by
-- proof
  apply StatMech.Walls.jc4_farDart_footprintAgree K


-- created on 2026-10-23
