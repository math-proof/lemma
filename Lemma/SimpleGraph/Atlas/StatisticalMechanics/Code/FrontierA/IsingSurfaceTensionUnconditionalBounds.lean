import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionUnconditionalBounds.Part2
open Filter Set Topology StatMech StatMech.FrontierA


/--
[rectangularIsingSurfaceTension_ge_meanfield_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionUnconditionalBounds.lean)
-/
@[path]
private lemma rectangularIsingSurfaceTension_ge_meanfield_increment_eq
  {a beta : Real}
-- given
  (ha : betaC 3 < a)
  (hab : a < beta) :
-- imply
  2 * (Real.sqrt (1 - (betaC 3 / a) ^ 2)) ^ 2 * (beta - a) <= rectangularIsingSurfaceTension beta := by
-- proof
  apply StatMech.FrontierA.rectangularIsingSurfaceTension_ge_meanfield_increment ha hab

/--
[cubicalInfiniteVolumeWilsonFreeEnergy_le_of_perimeterLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionUnconditionalBounds.lean)
-/
@[path]
private lemma cubicalInfiniteVolumeWilsonFreeEnergy_le_of_perimeterLower_eq
  {K C : Real}
  {n : Nat}
-- given
  (hK : 0 < K)
  (hlower : Real.exp (-C * centralSquareSide n) <= cubicalInfiniteVolumeWilsonExpectation K (centralSquareSide n) (centralSquareSide n)) :
-- imply
  cubicalInfiniteVolumeWilsonFreeEnergy K (centralSquareSide n) (centralSquareSide n) <= C * centralSquareSide n := by
-- proof
  apply StatMech.FrontierA.cubicalInfiniteVolumeWilsonFreeEnergy_le_of_perimeterLower hK n hlower

/--
[exists_cubicalInfiniteVolumeWilsonFreeEnergy_perimeterUpper_of_dual_lt_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionUnconditionalBounds.lean)
-/
@[path]
private lemma exists_cubicalInfiniteVolumeWilsonFreeEnergy_perimeterUpper_of_dual_lt_betaC_eq
  {K : Real}
-- given
  (hK : 0 < K)
  (hlt : gaugeDualCoupling K < betaC 3) :
-- imply
  ∃ C > 0, ∀ n, cubicalInfiniteVolumeWilsonFreeEnergy K (centralSquareSide n) (centralSquareSide n) <= C * centralSquareSide n := by
-- proof
  apply StatMech.FrontierA.exists_cubicalInfiniteVolumeWilsonFreeEnergy_perimeterUpper_of_dual_lt_betaC K hK hlt

/--
[cubicalInfiniteVolumeSquareWilsonDensity_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionUnconditionalBounds.lean)
-/
@[path]
private lemma cubicalInfiniteVolumeSquareWilsonDensity_nonneg_eq
  {K : Real}
  {n : Nat}
-- given
  (hK : 0 < K) :
-- imply
  0 <= cubicalInfiniteVolumeSquareWilsonDensity K n := by
-- proof
  apply StatMech.FrontierA.cubicalInfiniteVolumeSquareWilsonDensity_nonneg hK n

/--
[cubicalInfiniteVolumeSquareWilsonDensity_tendsto_zero_of_dual_lt_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionUnconditionalBounds.lean)
-/
@[path]
private lemma cubicalInfiniteVolumeSquareWilsonDensity_tendsto_zero_of_dual_lt_betaC_eq
  {K : Real}
-- given
  (hK : 0 < K)
  (hlt : gaugeDualCoupling K < betaC 3) :
-- imply
  Tendsto (cubicalInfiniteVolumeSquareWilsonDensity K) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.cubicalInfiniteVolumeSquareWilsonDensity_tendsto_zero_of_dual_lt_betaC K hK hlt


-- created on 2026-10-23
