import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeUnconditionalTransition
open Filter Topology StatMech StatMech.FrontierA


/--
[rectangularIsingSurfaceTension_pos_of_triple_tiling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeUnconditionalTransition.lean)
-/
@[path]
private lemma rectangularIsingSurfaceTension_pos_of_triple_tiling_eq
  {beta : Real}
-- given
  (hcritical : StatMech.Ising.betaC 3 < beta) :
-- imply
  0 < rectangularIsingSurfaceTension beta := by
-- proof
  apply StatMech.FrontierA.rectangularIsingSurfaceTension_pos_of_triple_tiling hcritical

/--
[cubicalSquareWilson_eventually_areaLaw_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeUnconditionalTransition.lean)
-/
@[path]
private lemma cubicalSquareWilson_eventually_areaLaw_unconditional_eq
  {K : Real}
-- given
  (hK : 0 < K)
  (hbelow : K < gaugeCriticalCoupling (StatMech.Ising.betaC 3)) :
-- imply
  ∀ᶠ n : Nat in atTop, cubicalSquareWilsonExpectation K n <= Real.exp (-(rectangularIsingSurfaceTension (gaugeDualCoupling K) / 2) * ((n + 1 : Nat) : Real) ^ 2) := by
-- proof
  apply StatMech.FrontierA.cubicalSquareWilson_eventually_areaLaw_unconditional hK hbelow

/--
[cubicalRectangularWilson_areaLaw_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeUnconditionalTransition.lean)
-/
@[path]
private lemma cubicalRectangularWilson_areaLaw_unconditional_eq
  {K : Real}
  {m n : Nat}
-- given
  (hK : 0 < K)
  (hbelow : K < gaugeCriticalCoupling (StatMech.Ising.betaC 3))
  (hm : 0 < m)
  (hn : 0 < n) :
-- imply
  0 < rectangularIsingSurfaceTension (gaugeDualCoupling K) /\ cubicalRectangularWilsonExpectation K m n <= Real.exp (-rectangularIsingSurfaceTension (gaugeDualCoupling K) * (m : Real) * (n : Real)) := by
-- proof
  apply StatMech.FrontierA.cubicalRectangularWilson_areaLaw_unconditional hK hbelow hm hn

/--
[cubicalSquareWilson_eventually_areaLaw_of_prismComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeUnconditionalTransition.lean)
-/
@[path]
private lemma cubicalSquareWilson_eventually_areaLaw_of_prismComparison_eq
  {K : Real}
-- given
  (hK : 0 < K)
  (hbelow : K < gaugeCriticalCoupling (StatMech.Ising.betaC 3))
  (hprism : HasPrismCubicalSurfaceComparison (gaugeDualCoupling K)) :
-- imply
  ∀ᶠ n : Nat in atTop, cubicalSquareWilsonExpectation K n <= Real.exp (-(rectangularIsingSurfaceTension (gaugeDualCoupling K) / 2) * ((n + 1 : Nat) : Real) ^ 2) := by
-- proof
  apply StatMech.FrontierA.cubicalSquareWilson_eventually_areaLaw_of_prismComparison hK hbelow hprism

/--
[cubicalSquareWilson_eventually_areaLaw_of_lower_ge_central](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeUnconditionalTransition.lean)
-/
@[path]
private lemma cubicalSquareWilson_eventually_areaLaw_of_lower_ge_central_eq
  {K : Real}
-- given
  (hK : 0 < K)
  (hbelow : K < gaugeCriticalCoupling (StatMech.Ising.betaC 3))
  (hposition : forall n, 0 < n -> centralCubicalIsingDisorderDensity (gaugeDualCoupling K) n <= oddCubicalIsingDisorderDensity (gaugeDualCoupling K) n) :
-- imply
  ∀ᶠ n : Nat in atTop, cubicalSquareWilsonExpectation K n <= Real.exp (-(rectangularIsingSurfaceTension (gaugeDualCoupling K) / 2) * ((n + 1 : Nat) : Real) ^ 2) := by
-- proof
  apply StatMech.FrontierA.cubicalSquareWilson_eventually_areaLaw_of_lower_ge_central hK hbelow hposition

/--
[cubicalZ2Gauge_unconditional_transition_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeUnconditionalTransition.lean)
-/
@[path]
private lemma cubicalZ2Gauge_unconditional_transition_data_eq
  {K : Real}
-- given
  (hK : 0 < K) :
-- imply
  (0 < gaugeCriticalCoupling (StatMech.Ising.betaC 3)) /\ (Real.cosh (gaugeCriticalCoupling (StatMech.Ising.betaC 3)) / Real.sinh (gaugeCriticalCoupling (StatMech.Ising.betaC 3)) = Real.exp (2 * StatMech.Ising.betaC 3)) /\ Tendsto (cubicalSquareWilsonDensity K) atTop (nhds (rectangularIsingSurfaceTension (gaugeDualCoupling K))) /\ (gaugeCriticalCoupling (StatMech.Ising.betaC 3) < K -> ∃ decay, 0 < decay ∧ ∀ n, Real.exp (-(gaugePerimeterPenalty (Real.exp (-decay)) * (20 * ((1 - Real.exp (-decay))⁻¹) ^ 3)) * centralSquareSide n) <= cubicalInfiniteVolumeWilsonExpectation K (centralSquareSide n) (centralSquareSide n)) := by
-- proof
  apply StatMech.FrontierA.cubicalZ2Gauge_unconditional_transition_data K hK

/--
[cubicalZ2Gauge_sharp_transition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeUnconditionalTransition.lean)
-/
@[path]
private lemma cubicalZ2Gauge_sharp_transition_eq
  {K : Real}
-- given
  (hK : 0 < K) :
-- imply
  (0 < gaugeCriticalCoupling (StatMech.Ising.betaC 3)) /\ (Real.cosh (gaugeCriticalCoupling (StatMech.Ising.betaC 3)) / Real.sinh (gaugeCriticalCoupling (StatMech.Ising.betaC 3)) = Real.exp (2 * StatMech.Ising.betaC 3)) /\ (rectangularSurfaceRate (cubicalRectangularWilsonFreeEnergy K) = rectangularIsingSurfaceTension (gaugeDualCoupling K)) /\ Tendsto (cubicalSquareWilsonDensity K) atTop (nhds (rectangularIsingSurfaceTension (gaugeDualCoupling K))) /\ (K < gaugeCriticalCoupling (StatMech.Ising.betaC 3) -> 0 < rectangularIsingSurfaceTension (gaugeDualCoupling K) /\ ∀ m n : Nat, 0 < m -> 0 < n -> cubicalRectangularWilsonExpectation K m n <= Real.exp (-rectangularIsingSurfaceTension (gaugeDualCoupling K) * (m : Real) * (n : Real))) /\ (gaugeCriticalCoupling (StatMech.Ising.betaC 3) < K -> ∃ decay, 0 < decay ∧ ∀ n, Real.exp (-(gaugePerimeterPenalty (Real.exp (-decay)) * (20 * ((1 - Real.exp (-decay))⁻¹) ^ 3)) * centralSquareSide n) <= cubicalInfiniteVolumeWilsonExpectation K (centralSquareSide n) (centralSquareSide n)) := by
-- proof
  apply StatMech.FrontierA.cubicalZ2Gauge_sharp_transition K hK


-- created on 2026-10-23
