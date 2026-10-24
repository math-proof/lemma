import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.QuantumIsingSectorBounds
open StatMech StatMech.FrontierA


/--
[anisotropicSquare_weightedSpin_norm_le_evenSubgraphSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSectorBounds.lean)
-/
@[path]
private lemma anisotropicSquare_weightedSpin_norm_le_evenSubgraphSum_eq
  {L : Nat}
  [Fact (2 < L)]
  {x y : Real}
  {a b : Fin 2}
-- given
  (hx : 0 ≤ x)
  (hy : 0 ≤ y) :
-- imply
  ‖ons_weightedSpinCharacterSum L (anisotropicSquareEdgeWeight L (x : Complex) (y : Complex)) a b‖ ≤ inhomogeneousEvenSubgraphSum (onsTorusGraph L) (fun edge => if squareTorusHorizontalEdge L edge then x else y) := by
-- proof
  apply StatMech.FrontierA.anisotropicSquare_weightedSpin_norm_le_evenSubgraphSum L hx hy a b

/--
[inhomogeneousEvenSubgraphSum_anisotropic_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSectorBounds.lean)
-/
@[path]
private lemma inhomogeneousEvenSubgraphSum_anisotropic_nonneg_eq
  {L : Nat}
  [Fact (2 < L)]
  {x y : Real}
-- given
  (hx : 0 ≤ x)
  (hy : 0 ≤ y) :
-- imply
  0 ≤ inhomogeneousEvenSubgraphSum (onsTorusGraph L) (fun edge => if squareTorusHorizontalEdge L edge then x else y) := by
-- proof
  apply StatMech.FrontierA.inhomogeneousEvenSubgraphSum_anisotropic_nonneg L hx hy

/--
[two_mul_evenSubgraphSum_le_sum_sector_norms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/QuantumIsingSectorBounds.lean)
-/
@[path]
private lemma two_mul_evenSubgraphSum_le_sum_sector_norms_eq
  {L : Nat}
  [Fact (2 < L)]
  {x y : Real}
-- given
  (hx : 0 ≤ x)
  (hy : 0 ≤ y) :
-- imply
  2 * inhomogeneousEvenSubgraphSum (onsTorusGraph L) (fun edge => if squareTorusHorizontalEdge L edge then x else y) ≤ ‖ons_weightedSpinCharacterSum L (anisotropicSquareEdgeWeight L (x : Complex) (y : Complex)) 1 1‖ + ‖ons_weightedSpinCharacterSum L (anisotropicSquareEdgeWeight L (x : Complex) (y : Complex)) 0 1‖ + ‖ons_weightedSpinCharacterSum L (anisotropicSquareEdgeWeight L (x : Complex) (y : Complex)) 1 0‖ + ‖ons_weightedSpinCharacterSum L (anisotropicSquareEdgeWeight L (x : Complex) (y : Complex)) 0 0‖ := by
-- proof
  apply StatMech.FrontierA.two_mul_evenSubgraphSum_le_sum_sector_norms L hx hy


-- created on 2026-10-23
