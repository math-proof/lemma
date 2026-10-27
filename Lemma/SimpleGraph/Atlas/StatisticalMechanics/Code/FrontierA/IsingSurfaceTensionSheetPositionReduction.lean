import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetPositionReduction
open Filter Set Topology StatMech StatMech.FrontierA


/--
[oddCubicalIsingDisorderDensity_eq_lowerSheetFreeEnergy_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSheetPositionReduction.lean)
-/
@[path]
private lemma oddCubicalIsingDisorderDensity_eq_lowerSheetFreeEnergy_div_eq
  {beta : Real}
  {n : Nat}
-- given
  (hbeta : 0 < beta) :
-- imply
  oddCubicalIsingDisorderDensity beta n = oddCubicalLowerSheetFreeEnergy beta n / (((2 * n + 1 : Nat) : Real) ^ 2) := by
-- proof
  apply StatMech.FrontierA.oddCubicalIsingDisorderDensity_eq_lowerSheetFreeEnergy_div hbeta n

/--
[centralCubicalIsingDisorderDensity_eq_centralSheetFreeEnergy_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSheetPositionReduction.lean)
-/
@[path]
private lemma centralCubicalIsingDisorderDensity_eq_centralSheetFreeEnergy_div_eq
  {beta : Real}
  {n : Nat} :
-- imply
  centralCubicalIsingDisorderDensity beta n = oddCubicalCentralSheetFreeEnergy beta n / (((2 * n + 1 : Nat) : Real) ^ 2) := by
-- proof
  apply StatMech.FrontierA.centralCubicalIsingDisorderDensity_eq_centralSheetFreeEnergy_div beta n

/--
[hasPrismCubicalSurfaceComparison_of_perimeter_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSheetPositionReduction.lean)
-/
@[path]
private lemma hasPrismCubicalSurfaceComparison_of_perimeter_bound_eq
  {beta C : Real}
-- given
  (hbeta : 0 < beta)
  (hbound : forall n, 0 < n -> |oddCubicalCentralSheetFreeEnergy beta n - oddCubicalLowerSheetFreeEnergy beta n| <= C * ((2 * n + 1 : Nat) : Real)) :
-- imply
  HasPrismCubicalSurfaceComparison beta := by
-- proof
  apply StatMech.FrontierA.hasPrismCubicalSurfaceComparison_of_perimeter_bound hbeta hbound

/--
[rectangularIsingSurfaceTension_pos_of_lower_ge_central](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSheetPositionReduction.lean)
-/
@[path]
private lemma rectangularIsingSurfaceTension_pos_of_lower_ge_central_eq
  {beta : Real}
-- given
  (hcritical : StatMech.Ising.betaC 3 < beta)
  (hposition : forall n, 0 < n -> centralCubicalIsingDisorderDensity beta n <= oddCubicalIsingDisorderDensity beta n) :
-- imply
  0 < rectangularIsingSurfaceTension beta := by
-- proof
  apply StatMech.FrontierA.rectangularIsingSurfaceTension_pos_of_lower_ge_central hcritical hposition


-- created on 2026-10-23
