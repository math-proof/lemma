import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossingCounterexample
open SimpleGraph Set StatMech StatMech.BeffaraDC


/--
[torusSquareShiftCounterexample_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossingCounterexample.lean)
-/
@[path]
private lemma torusSquareShiftCounterexample_horizontal_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  torusSquareHorizontalCrossing L 1 (torusSquareShiftCounterexampleConfig L) := by
-- proof
  apply StatMech.BeffaraDC.torusSquareShiftCounterexample_horizontal L

/--
[torusSquareShiftCounterexample_dual_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossingCounterexample.lean)
-/
@[path]
private lemma torusSquareShiftCounterexample_dual_vertical_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  torusCellDualAmbientConfig L (torusSquareShiftCounterexampleConfig L) ∈ torusSquareVerticalCrossingEvent L 1 := by
-- proof
  apply StatMech.BeffaraDC.torusSquareShiftCounterexample_dual_vertical L

/--
[torus_concreteSquareCrossing_duality_iff_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossingCounterexample.lean)
-/
@[path]
private lemma torus_concreteSquareCrossing_duality_iff_false_eq
  {L : ℕ}
  [Fact (2 < L)] :
-- imply
  ¬ ∀ omega : TorusAmbientConfig L, ¬ torusSquareHorizontalCrossing L 1 omega ↔ torusCellDualAmbientConfig L omega ∈ torusSquareVerticalCrossingEvent L 1 := by
-- proof
  apply StatMech.BeffaraDC.torus_concreteSquareCrossing_duality_iff_false L

/--
[torus_squareCrossing_ge_one_div_one_add_q_of_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossingCounterexample.lean)
-/
@[path]
private lemma torus_squareCrossing_ge_one_div_one_add_q_of_cover_eq
  {L : ℕ}
  [Fact (2 < L)]
  {q : ℝ}
-- given
  (horizontal : Finset (TorusAmbientConfig L))
  (hq1 : 1 ≤ q)
  (hdualCrossing : ∀ omega : TorusAmbientConfig L, omega ∉ horizontal → torusCellDualAmbientConfig L omega ∈ torusAmbientRotatedEvent L horizontal) :
-- imply
  1 / (1 + q) ≤ torusAmbientEventProbability L (selfDualPoint q) q horizontal := by
-- proof
  apply StatMech.BeffaraDC.torus_squareCrossing_ge_one_div_one_add_q_of_cover L horizontal hq1 hdualCrossing

/--
[torus_concreteSquareCrossing_ge_one_div_one_add_q_of_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossingCounterexample.lean)
-/
@[path]
private lemma torus_concreteSquareCrossing_ge_one_div_one_add_q_of_cover_eq
  {L : ℕ}
  [Fact (2 < L)]
  {n : ℕ}
  {q : ℝ}
-- given
  (_hn : 1 ≤ n)
  (_hnL : n < L)
  (hq1 : 1 ≤ q)
  (hdualCrossing : ∀ omega : TorusAmbientConfig L, ¬ torusSquareHorizontalCrossing L n omega → torusCellDualAmbientConfig L omega ∈ torusSquareVerticalCrossingEvent L n) :
-- imply
  1 / (1 + q) ≤ torusAmbientEventProbability L (selfDualPoint q) q (torusSquareHorizontalCrossingEvent L n) := by
-- proof
  apply StatMech.BeffaraDC.torus_concreteSquareCrossing_ge_one_div_one_add_q_of_cover L n _hn _hnL hq1 hdualCrossing


-- created on 2026-10-23
