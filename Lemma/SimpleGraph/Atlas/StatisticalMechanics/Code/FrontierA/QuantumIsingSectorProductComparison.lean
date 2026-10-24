import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.QuantumIsingSectorProductComparison
open StatMech StatMech.FrontierA


/--
[quantumIsingNormalizedSpinSector_sq_eq_reducedSectorProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSectorProductComparison.lean)
-/
@[path]
private lemma quantumIsingNormalizedSpinSector_sq_eq_reducedSectorProduct_eq
  {L : Nat}
  [Fact (2 < L)]
  {a b : Fin 2}
-- given
  (beta h : Real)
  (hx : 0 < beta * h / (2 * L))
  (hx1 : beta * h / (2 * L) < 1) :
-- imply
  quantumIsingNormalizedSpinSector beta h L a b ^ 2 = (quantumIsingReducedSectorProduct beta h L a b : Complex) := by
-- proof
  apply StatMech.FrontierA.quantumIsingNormalizedSpinSector_sq_eq_reducedSectorProduct beta h L a b hx hx1

/--
[quantumIsingReducedSectorProduct_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSectorProductComparison.lean)
-/
@[path]
private lemma quantumIsingReducedSectorProduct_nonneg_eq
  {L : Nat}
  [Fact (2 < L)]
  {a b : Fin 2}
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hx : 0 < beta * h / (2 * L))
  (hx1 : beta * h / (2 * L) < 1) :
-- imply
  0 ≤ quantumIsingReducedSectorProduct beta h L a b := by
-- proof
  apply StatMech.FrontierA.quantumIsingReducedSectorProduct_nonneg beta h L a b hbeta hx hx1

/--
[quantumIsingReducedSectorProduct_periodic_le_antiperiodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSectorProductComparison.lean)
-/
@[path]
private lemma quantumIsingReducedSectorProduct_periodic_le_antiperiodic_eq
  {L : Nat}
  [Fact (2 < L)]
  {a : Fin 2}
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hx : 0 < beta * h / (2 * L))
  (hx1 : beta * h / (2 * L) < 1) :
-- imply
  quantumIsingReducedSectorProduct beta h L a 0 ≤ quantumIsingReducedSectorProduct beta h L a 1 := by
-- proof
  apply StatMech.FrontierA.quantumIsingReducedSectorProduct_periodic_le_antiperiodic beta h L a hbeta hx hx1

/--
[quantumIsingNormalizedSpinSector_periodic_norm_le_antiperiodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSectorProductComparison.lean)
-/
@[path]
private lemma quantumIsingNormalizedSpinSector_periodic_norm_le_antiperiodic_eq
  {L : Nat}
  [Fact (2 < L)]
  {a : Fin 2}
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hx : 0 < beta * h / (2 * L))
  (hx1 : beta * h / (2 * L) < 1) :
-- imply
  ‖quantumIsingNormalizedSpinSector beta h L a 0‖ ≤ ‖quantumIsingNormalizedSpinSector beta h L a 1‖ := by
-- proof
  apply StatMech.FrontierA.quantumIsingNormalizedSpinSector_periodic_norm_le_antiperiodic beta h L a hbeta hx hx1

/--
[quantumIsingReducedSectorProduct_spatialPeriodic_le_antiperiodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSectorProductComparison.lean)
-/
@[path]
private lemma quantumIsingReducedSectorProduct_spatialPeriodic_le_antiperiodic_eq
  {L : Nat}
  [Fact (2 < L)]
  {b : Fin 2}
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hh : 0 < h)
  (hx : 0 < beta * h / (2 * L))
  (hx1 : beta * h / (2 * L) < 1) :
-- imply
  quantumIsingReducedSectorProduct beta h L 0 b ≤ quantumIsingReducedSectorProduct beta h L 1 b := by
-- proof
  apply StatMech.FrontierA.quantumIsingReducedSectorProduct_spatialPeriodic_le_antiperiodic beta h L b hbeta hh hx hx1

/--
[quantumIsingNormalizedSpinSector_spatialPeriodic_norm_le_antiperiodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSectorProductComparison.lean)
-/
@[path]
private lemma quantumIsingNormalizedSpinSector_spatialPeriodic_norm_le_antiperiodic_eq
  {L : Nat}
  [Fact (2 < L)]
  {b : Fin 2}
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hh : 0 < h)
  (hx : 0 < beta * h / (2 * L))
  (hx1 : beta * h / (2 * L) < 1) :
-- imply
  ‖quantumIsingNormalizedSpinSector beta h L 0 b‖ ≤ ‖quantumIsingNormalizedSpinSector beta h L 1 b‖ := by
-- proof
  apply StatMech.FrontierA.quantumIsingNormalizedSpinSector_spatialPeriodic_norm_le_antiperiodic beta h L b hbeta hh hx hx1

/--
[arfSectorNormMax_quantumIsingNormalizedSpinSector_eq_eleven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSectorProductComparison.lean)
-/
@[path]
private lemma arfSectorNormMax_quantumIsingNormalizedSpinSector_eq_eleven_eq
  {L : Nat}
  [Fact (2 < L)]
-- given
  (beta h : Real)
  (hbeta : 0 < beta)
  (hh : 0 < h)
  (hx : 0 < beta * h / (2 * L))
  (hx1 : beta * h / (2 * L) < 1) :
-- imply
  arfSectorNormMax (quantumIsingNormalizedSpinSector beta h L) = ‖quantumIsingNormalizedSpinSector beta h L 1 1‖ := by
-- proof
  apply StatMech.FrontierA.arfSectorNormMax_quantumIsingNormalizedSpinSector_eq_eleven beta h L hbeta hh hx hx1


-- created on 2026-10-23
