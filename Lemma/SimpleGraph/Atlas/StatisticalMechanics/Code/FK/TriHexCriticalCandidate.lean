import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.TriHexCriticalCandidate
open Set StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[exists_triangularFKCritical_candidate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCriticalCandidate.lean)
-/
@[path]
private lemma exists_triangularFKCritical_candidate_eq
  {q : Real}
-- given
  (hq : 1 <= q) :
-- imply
  exists p : Real, p ∈ Ioo (0 : Real) 1 /\ triangularFKCriticalPolynomial q (fkEdgeOdds p) = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_triangularFKCritical_candidate hq

/--
[exists_triangularFKCritical_candidate_weaklyAligned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCriticalCandidate.lean)
-/
@[path]
private lemma exists_triangularFKCritical_candidate_weaklyAligned_eq
  {q : Real}
-- given
  (hq : 1 <= q) :
-- imply
  exists p : Real, p ∈ Ioo (0 : Real) 1 /\ triangularFKCriticalPolynomial q (fkEdgeOdds p) = 0 /\ (p < triangular.criticalPoint q -> dualParam p q <= hexagonal.criticalPoint q) /\ (triangular.criticalPoint q < p -> hexagonal.criticalPoint q <= dualParam p q) /\ (dualParam p q < hexagonal.criticalPoint q -> p <= triangular.criticalPoint q) /\ (hexagonal.criticalPoint q < dualParam p q -> triangular.criticalPoint q <= p) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_triangularFKCritical_candidate_weaklyAligned hq


-- created on 2026-10-23
