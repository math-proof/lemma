import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionFiniteInfiniteGap.Part2
open Filter Topology StatMech StatMech.FrontierA


/--
[cubicalSquareWilsonExpectation_le_fixedLoopSequence_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionFiniteInfiniteGap.lean)
-/
@[path]
private lemma cubicalSquareWilsonExpectation_le_fixedLoopSequence_self_eq
  {K : Real}
  {n : Nat}
-- given
  (hK : 0 < K) :
-- imply
  cubicalSquareWilsonExpectation K n <= cubicalFixedLoopWilsonSequence K (n + 1) (n + 1) (n + 1) := by
-- proof
  apply StatMech.FrontierA.cubicalSquareWilsonExpectation_le_fixedLoopSequence_self hK n

/--
[cubicalSquareWilsonExpectation_le_infiniteVolume](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionFiniteInfiniteGap.lean)
-/
@[path]
private lemma cubicalSquareWilsonExpectation_le_infiniteVolume_eq
  {K : Real}
  {n : Nat}
-- given
  (hK : 0 < K) :
-- imply
  cubicalSquareWilsonExpectation K n <= cubicalInfiniteVolumeWilsonExpectation K (n + 1) (n + 1) := by
-- proof
  apply StatMech.FrontierA.cubicalSquareWilsonExpectation_le_infiniteVolume hK n

/--
[cubicalInfiniteVolumeSquareWilsonDensity_le_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionFiniteInfiniteGap.lean)
-/
@[path]
private lemma cubicalInfiniteVolumeSquareWilsonDensity_le_finite_eq
  {K : Real}
  {n : Nat}
-- given
  (hK : 0 < K) :
-- imply
  cubicalInfiniteVolumeSquareWilsonDensity K n <= cubicalSquareWilsonDensity K n := by
-- proof
  apply StatMech.FrontierA.cubicalInfiniteVolumeSquareWilsonDensity_le_finite hK n

/--
[cubicalFiniteInfiniteSquareDensityGap_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionFiniteInfiniteGap.lean)
-/
@[path]
private lemma cubicalFiniteInfiniteSquareDensityGap_nonneg_eq
  {K : Real}
  {n : Nat}
-- given
  (hK : 0 < K) :
-- imply
  0 <= cubicalFiniteInfiniteSquareDensityGap K n := by
-- proof
  apply StatMech.FrontierA.cubicalFiniteInfiniteSquareDensityGap_nonneg hK n

/--
[cubicalFiniteInfiniteSquareDensityGap_tendsto_surfaceTension](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionFiniteInfiniteGap.lean)
-/
@[path]
private lemma cubicalFiniteInfiniteSquareDensityGap_tendsto_surfaceTension_eq
  {K : Real}
-- given
  (hK : 0 < K)
  (hlt : gaugeDualCoupling K < StatMech.Ising.betaC 3) :
-- imply
  Tendsto (cubicalFiniteInfiniteSquareDensityGap K) atTop (nhds (rectangularIsingSurfaceTension (gaugeDualCoupling K))) := by
-- proof
  apply StatMech.FrontierA.cubicalFiniteInfiniteSquareDensityGap_tendsto_surfaceTension K hK hlt

/--
[rectangularIsingSurfaceTension_eq_zero_iff_gap_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionFiniteInfiniteGap.lean)
-/
@[path]
private lemma rectangularIsingSurfaceTension_eq_zero_iff_gap_tendsto_zero_eq
  {K : Real}
-- given
  (hK : 0 < K)
  (hlt : gaugeDualCoupling K < StatMech.Ising.betaC 3) :
-- imply
  rectangularIsingSurfaceTension (gaugeDualCoupling K) = 0 <-> Tendsto (cubicalFiniteInfiniteSquareDensityGap K) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.rectangularIsingSurfaceTension_eq_zero_iff_gap_tendsto_zero K hK hlt


-- created on 2026-10-23
