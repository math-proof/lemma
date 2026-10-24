import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.Z2GaugeDiagonalBoundaryApproximation
open Filter Topology StatMech StatMech.FrontierA


/--
[cubicalInfiniteVolumeWilsonFreeEnergy_le_paddedDisorderFreeEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDiagonalBoundaryApproximation.lean)
-/
@[path]
private lemma cubicalInfiniteVolumeWilsonFreeEnergy_le_paddedDisorderFreeEnergy_eq
  {K : Real}
  {a b lx rx ly ry lz rz : Nat}
-- given
  (hK : 0 < K)
  (ha : 0 < a)
  (hb : 0 < b)
  (hz : 0 < lz + rz) :
-- imply
  cubicalInfiniteVolumeWilsonFreeEnergy K a b <= cubicalPaddedDisorderFreeEnergy K a b lx rx ly ry lz rz := by
-- proof
  apply StatMech.FrontierA.cubicalInfiniteVolumeWilsonFreeEnergy_le_paddedDisorderFreeEnergy hK ha hb hz

/--
[exists_cubicalPaddedDisorderDensity_close_infiniteVolume](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDiagonalBoundaryApproximation.lean)
-/
@[path]
private lemma exists_cubicalPaddedDisorderDensity_close_infiniteVolume_eq
  {K : Real}
  {n : Nat}
  {eps : Real}
-- given
  (hK : 0 < K)
  (heps : 0 < eps) :
-- imply
  exists m : Nat, 0 < m /\ 0 <= cubicalPaddedDisorderFreeEnergy K (centralSquareSide n) (centralSquareSide n) m m m m m m / ((centralSquareSide n : Nat) : Real) ^ 2 - cubicalInfiniteVolumeSquareWilsonDensity K n /\ cubicalPaddedDisorderFreeEnergy K (centralSquareSide n) (centralSquareSide n) m m m m m m / ((centralSquareSide n : Nat) : Real) ^ 2 - cubicalInfiniteVolumeSquareWilsonDensity K n < eps := by
-- proof
  apply StatMech.FrontierA.exists_cubicalPaddedDisorderDensity_close_infiniteVolume hK n heps

/--
[cubicalDiagonalApproximationPadding_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDiagonalBoundaryApproximation.lean)
-/
@[path]
private lemma cubicalDiagonalApproximationPadding_spec_eq
  {K : Real}
  {n : Nat}
-- given
  (hK : 0 < K) :
-- imply
  0 < cubicalDiagonalApproximationPadding hK n /\ 0 <= cubicalDiagonalFiniteInfiniteDensityGap hK n /\ cubicalDiagonalFiniteInfiniteDensityGap hK n < (1 : Real) / ((centralSquareSide n : Nat) : Real) := by
-- proof
  apply StatMech.FrontierA.cubicalDiagonalApproximationPadding_spec hK n

/--
[cubicalDiagonalFiniteInfiniteDensityGap_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDiagonalBoundaryApproximation.lean)
-/
@[path]
private lemma cubicalDiagonalFiniteInfiniteDensityGap_tendsto_zero_eq
  {K : Real}
-- given
  (hK : 0 < K) :
-- imply
  Tendsto (cubicalDiagonalFiniteInfiniteDensityGap hK) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.cubicalDiagonalFiniteInfiniteDensityGap_tendsto_zero hK

/--
[cubicalDiagonalPaddedDisorderDensity_tendsto_zero_of_dual_lt_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDiagonalBoundaryApproximation.lean)
-/
@[path]
private lemma cubicalDiagonalPaddedDisorderDensity_tendsto_zero_of_dual_lt_betaC_eq
  {K : Real}
-- given
  (hK : 0 < K)
  (hlt : gaugeDualCoupling K < StatMech.Ising.betaC 3) :
-- imply
  Tendsto (fun n : Nat => let m := cubicalDiagonalApproximationPadding hK n cubicalPaddedDisorderFreeEnergy K (centralSquareSide n) (centralSquareSide n) m m m m m m / ((centralSquareSide n : Nat) : Real) ^ 2) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.cubicalDiagonalPaddedDisorderDensity_tendsto_zero_of_dual_lt_betaC K hK hlt


-- created on 2026-10-23
