import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterTwoGhostVarianceSector
open StatMech StatMech.Ising


/--
[lpTwoGhost_sectorVariance_sub_clear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoGhostVarianceSector.lean)
-/
@[path]
private lemma lpTwoGhost_sectorVariance_sub_clear_eq
  {a b c d e : Real}
-- given
  (hplus : Ne (1 + c) 0)
  (hminus : Ne (1 - c) 0) :
-- imply
  (1 - c ^ 2) ^ 2 * (lpTwoGhostPlusSectorVariance a b c d e - lpTwoGhostMinusSectorVariance a b c d e) = 2 * ((1 - c ^ 2) * ((e - d * c) - 2 * a * (b - a * c)) + 2 * c * (b - a * c) ^ 2) := by
-- proof
  apply StatMech.Ising.lpTwoGhost_sectorVariance_sub_clear a b c d e hplus hminus

/--
[lpTwoGhost_centeredCovariance_clear_current](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterTwoGhostVarianceSector.lean)
-/
@[path]
private lemma lpTwoGhost_centeredCovariance_clear_current_eq
  {A B C D E Z : Real}
-- given
  (hZ : Ne Z 0) :
-- imply
  (1 - (C / Z) ^ 2) * (((E / Z) - (D / Z) * (C / Z)) - 2 * (A / Z) * ((B / Z) - (A / Z) * (C / Z))) + 2 * (C / Z) * ((B / Z) - (A / Z) * (C / Z)) ^ 2 = ((Z ^ 2 - C ^ 2) * (((E * Z - D * C) * Z) - 2 * A * (B * Z - A * C)) + 2 * C * (B * Z - A * C) ^ 2) / Z ^ 5 := by
-- proof
  apply StatMech.Ising.lpTwoGhost_centeredCovariance_clear_current A B C D E Z hZ


-- created on 2026-10-23
