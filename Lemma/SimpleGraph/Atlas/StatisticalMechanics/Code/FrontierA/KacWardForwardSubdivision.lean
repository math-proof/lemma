import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardForwardSubdivision
open StatMech StatMech.FrontierA


/--
[KWRawTurnAdmissible.adjacent_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardForwardSubdivision.lean)
-/
@[path]
private lemma adjacent_disjoint_eq
  {n : ℕ}
  [NeZero n]
  {vertex : Fin n → ℂ}
  {i : Fin n}
-- given
  (hedge : ∀ i : Fin n, kwRawEdge vertex i ≠ 0)
  (h : KWRawTurnAdmissible vertex i) :
-- imply
  Disjoint {z : ℂ | Sbtw ℝ (vertex i) z (vertex (i + 1))} {z : ℂ | Sbtw ℝ (vertex (i + 1)) z (vertex (i + 2))} := by
-- proof
  apply StatMech.FrontierA.KWRawTurnAdmissible.adjacent_disjoint hedge h

/--
[KWRawTurnAdmissible.previous_not_between](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardForwardSubdivision.lean)
-/
@[path]
private lemma previous_not_between_eq
  {n : ℕ}
  [NeZero n]
  {vertex : Fin n → ℂ}
  {i : Fin n}
-- given
  (hedge : ∀ i : Fin n, kwRawEdge vertex i ≠ 0)
  (h : KWRawTurnAdmissible vertex i) :
-- imply
  ¬Sbtw ℝ (vertex (i + 1)) (vertex i) (vertex (i + 2)) := by
-- proof
  apply StatMech.FrontierA.KWRawTurnAdmissible.previous_not_between hedge h

/--
[KWRawNonbacktrackingSimpleData.of_turnAdmissible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardForwardSubdivision.lean)
-/
@[path]
private lemma of_turnAdmissible_eq
  {n : ℕ}
  [NeZero n]
  {vertex : Fin n → ℂ}
-- given
  (hthree : 3 ≤ n)
  (hedge : ∀ i : Fin n, kwRawEdge vertex i ≠ 0)
  (hturn : ∀ i : Fin n, KWRawTurnAdmissible vertex i)
  (hnon : ∀ i j : Fin n, KWEdgesNonincident i j → Disjoint (kwRawClosedEdge vertex i) (kwRawClosedEdge vertex j)) :
-- imply
  KWRawNonbacktrackingSimpleData vertex where three_le := by
-- proof
  apply StatMech.FrontierA.KWRawNonbacktrackingSimpleData.of_turnAdmissible vertex hthree hedge hturn hnon


-- created on 2026-10-23
