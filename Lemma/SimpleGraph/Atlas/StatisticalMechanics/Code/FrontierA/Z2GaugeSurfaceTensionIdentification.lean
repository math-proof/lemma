import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeSurfaceTensionIdentification
open Filter Topology StatMech StatMech.FrontierA


/--
[gaugeCriticalCoupling_gaugeDualCoupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeSurfaceTensionIdentification.lean)
-/
@[path]
private lemma gaugeCriticalCoupling_gaugeDualCoupling_eq
  {beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  gaugeCriticalCoupling (gaugeDualCoupling beta) = beta := by
-- proof
  apply StatMech.FrontierA.gaugeCriticalCoupling_gaugeDualCoupling hbeta

/--
[rectangularIsingDobrushinFreeEnergy_gaugeDualCoupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeSurfaceTensionIdentification.lean)
-/
@[path]
private lemma rectangularIsingDobrushinFreeEnergy_gaugeDualCoupling_eq
  {beta : Real}
  {m n : Nat}
-- given
  (hbeta : 0 < beta) :
-- imply
  rectangularIsingDobrushinFreeEnergy (gaugeDualCoupling beta) m n = cubicalRectangularWilsonFreeEnergy beta m n := by
-- proof
  apply StatMech.FrontierA.rectangularIsingDobrushinFreeEnergy_gaugeDualCoupling hbeta m n

/--
[cubicalRectangularWilsonFreeEnergy_eq_finiteIsingDisorder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeSurfaceTensionIdentification.lean)
-/
@[path]
private lemma cubicalRectangularWilsonFreeEnergy_eq_finiteIsingDisorder_eq
  {beta : Real}
  {m n : Nat}
-- given
  (hbeta : 0 < beta)
  (hm : 0 < m)
  (hn : 0 < n) :
-- imply
  cubicalRectangularWilsonFreeEnergy beta m n = finiteRectangularIsingDisorderFreeEnergy (gaugeDualCoupling beta) m n := by
-- proof
  apply StatMech.FrontierA.cubicalRectangularWilsonFreeEnergy_eq_finiteIsingDisorder hbeta hm hn

/--
[cubicalRectangularWilsonSurfaceRate_eq_rectangularIsingSurfaceTension](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeSurfaceTensionIdentification.lean)
-/
@[path]
private lemma cubicalRectangularWilsonSurfaceRate_eq_rectangularIsingSurfaceTension_eq
  {beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  rectangularSurfaceRate (cubicalRectangularWilsonFreeEnergy beta) = rectangularIsingSurfaceTension (gaugeDualCoupling beta) := by
-- proof
  apply StatMech.FrontierA.cubicalRectangularWilsonSurfaceRate_eq_rectangularIsingSurfaceTension hbeta

/--
[cubicalSquareWilsonDensity_tendsto_rectangularIsingSurfaceTension](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeSurfaceTensionIdentification.lean)
-/
@[path]
private lemma cubicalSquareWilsonDensity_tendsto_rectangularIsingSurfaceTension_eq
  {beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  Tendsto (cubicalSquareWilsonDensity beta) atTop (nhds (rectangularIsingSurfaceTension (gaugeDualCoupling beta))) := by
-- proof
  apply StatMech.FrontierA.cubicalSquareWilsonDensity_tendsto_rectangularIsingSurfaceTension hbeta

/--
[cubicalSquareDisorderDensity_tendsto_rectangularIsingSurfaceTension](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeSurfaceTensionIdentification.lean)
-/
@[path]
private lemma cubicalSquareDisorderDensity_tendsto_rectangularIsingSurfaceTension_eq
  {beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  Tendsto (cubicalSquareDisorderDensity beta) atTop (nhds (rectangularIsingSurfaceTension (gaugeDualCoupling beta))) := by
-- proof
  apply StatMech.FrontierA.cubicalSquareDisorderDensity_tendsto_rectangularIsingSurfaceTension hbeta

/--
[cubicalRectangularWilsonSurfaceRate_pos_iff_below_critical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeSurfaceTensionIdentification.lean)
-/
@[path]
private lemma cubicalRectangularWilsonSurfaceRate_pos_iff_below_critical_eq
  {beta betaIsingC : Real}
-- given
  (hbeta : 0 < beta)
  (hIsingC : 0 < betaIsingC)
  (hphase : 0 < rectangularIsingSurfaceTension (gaugeDualCoupling beta) <-> betaIsingC < gaugeDualCoupling beta) :
-- imply
  0 < rectangularSurfaceRate (cubicalRectangularWilsonFreeEnergy beta) <-> beta < gaugeCriticalCoupling betaIsingC := by
-- proof
  apply StatMech.FrontierA.cubicalRectangularWilsonSurfaceRate_pos_iff_below_critical hbeta hIsingC hphase

/--
[cubicalSquareWilson_eventually_areaLaw_of_rectangularIsing_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeSurfaceTensionIdentification.lean)
-/
@[path]
private lemma cubicalSquareWilson_eventually_areaLaw_of_rectangularIsing_phase_eq
  {beta betaIsingC : Real}
-- given
  (hbeta : 0 < beta)
  (hIsingC : 0 < betaIsingC)
  (hphase : 0 < rectangularIsingSurfaceTension (gaugeDualCoupling beta) <-> betaIsingC < gaugeDualCoupling beta)
  (hbelow : beta < gaugeCriticalCoupling betaIsingC) :
-- imply
  ∀ᶠ n : Nat in atTop, cubicalSquareWilsonExpectation beta n <= Real.exp (-(rectangularIsingSurfaceTension (gaugeDualCoupling beta) / 2) * ((n + 1 : Nat) : Real) ^ 2) := by
-- proof
  apply StatMech.FrontierA.cubicalSquareWilson_eventually_areaLaw_of_rectangularIsing_phase hbeta hIsingC hphase hbelow

/--
[standardCubicInterfaceDensity_tendsto_cubicalWilsonSurfaceRate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeSurfaceTensionIdentification.lean)
-/
@[path]
private lemma standardCubicInterfaceDensity_tendsto_cubicalWilsonSurfaceRate_eq
  {beta : Real}
-- given
  (hbeta : 0 < beta)
  (hprism : HasPrismCubicalSurfaceComparison beta)
  (hstandard : HasStandardPrismSurfaceComparison beta) :
-- imply
  Tendsto (standardCubicInterfaceDensity beta) atTop (nhds (rectangularSurfaceRate (cubicalRectangularWilsonFreeEnergy (gaugeCriticalCoupling beta)))) := by
-- proof
  apply StatMech.FrontierA.standardCubicInterfaceDensity_tendsto_cubicalWilsonSurfaceRate hbeta hprism hstandard

/--
[cubicalSquareWilson_eventually_areaLaw_of_weak_LebowitzPfister](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeSurfaceTensionIdentification.lean)
-/
@[path]
private lemma cubicalSquareWilson_eventually_areaLaw_of_weak_LebowitzPfister_eq
  {betaGauge betaIsingC : Real}
-- given
  (hGauge : 0 < betaGauge)
  (hIsingC : 0 < betaIsingC)
  (hregime : StatMech.Ising.HasOrderedMagnetizationRegime (StatMech.Ising.magnetization 3) betaIsingC)
  (hupper : forall beta, 0 < beta -> rectangularIsingSurfaceTension beta <= 2 * beta * (StatMech.Ising.magnetization 3 beta) ^ 2)
  (hweak : StatMech.Ising.HasWeakSurfaceTensionLowerBound 1 (StatMech.Ising.magnetization 3) rectangularIsingSurfaceTension)
  (hbelow : betaGauge < gaugeCriticalCoupling betaIsingC) :
-- imply
  ∀ᶠ n : Nat in atTop, cubicalSquareWilsonExpectation betaGauge n <= Real.exp (-(rectangularIsingSurfaceTension (gaugeDualCoupling betaGauge) / 2) * ((n + 1 : Nat) : Real) ^ 2) := by
-- proof
  apply StatMech.FrontierA.cubicalSquareWilson_eventually_areaLaw_of_weak_LebowitzPfister hGauge hIsingC hregime hupper hweak hbelow

/--
[cubicalSquareWilson_eventually_areaLaw_of_standard_interface_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeSurfaceTensionIdentification.lean)
-/
@[path]
private lemma cubicalSquareWilson_eventually_areaLaw_of_standard_interface_bounds_eq
  {betaGauge betaIsingC : Real}
-- given
  (hGauge : 0 < betaGauge)
  (hIsingC : 0 < betaIsingC)
  (hregime : StatMech.Ising.HasOrderedMagnetizationRegime (StatMech.Ising.magnetization 3) betaIsingC)
  (hprism : forall beta, 0 < beta -> HasPrismCubicalSurfaceComparison beta)
  (hstandard : forall beta, 0 < beta -> HasStandardPrismSurfaceComparison beta)
  (hupper : forall n beta, 0 < beta -> standardCubicInterfaceDensity beta n <= 2 * beta * (StatMech.Ising.magnetization 3 beta) ^ 2)
  (hweak : forall n, StatMech.Ising.HasWeakSurfaceTensionLowerBound 1 (StatMech.Ising.magnetization 3) (fun beta => standardCubicInterfaceDensity beta n))
  (hbelow : betaGauge < gaugeCriticalCoupling betaIsingC) :
-- imply
  ∀ᶠ n : Nat in atTop, cubicalSquareWilsonExpectation betaGauge n <= Real.exp (-(rectangularIsingSurfaceTension (gaugeDualCoupling betaGauge) / 2) * ((n + 1 : Nat) : Real) ^ 2) := by
-- proof
  apply StatMech.FrontierA.cubicalSquareWilson_eventually_areaLaw_of_standard_interface_bounds hGauge hIsingC hregime hprism hstandard hupper hweak hbelow


-- created on 2026-10-23
