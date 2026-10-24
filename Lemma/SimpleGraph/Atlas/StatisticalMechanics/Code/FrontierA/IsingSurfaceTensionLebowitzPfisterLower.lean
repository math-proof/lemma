import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionLebowitzPfisterLower
open Filter Set Topology StatMech StatMech.FrontierA


/--
[hasDerivAt_standardCubicInterfaceDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionLebowitzPfisterLower.lean)
-/
@[path]
private lemma hasDerivAt_standardCubicInterfaceDensity_eq
  {beta : Real}
  {n : Nat} :
-- imply
  HasDerivAt (fun b => standardCubicInterfaceDensity b n) ((fvMeanNegEnergy (plusField 3) n (bondFinsetTouch 3 n) beta 0 - fvMeanNegEnergy (interfaceField (⟨2, by omega⟩ : Fin 3)) n (bondFinsetTouch 3 n) beta 0) / ((2 * n + 1 : Nat) : Real) ^ 2) beta := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_standardCubicInterfaceDensity beta n

/--
[standardCubicInterfaceDensity_deriv_ge_two_mul_sq_of_energyDeficit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionLebowitzPfisterLower.lean)
-/
@[path]
private lemma standardCubicInterfaceDensity_deriv_ge_two_mul_sq_of_energyDeficit_eq
  {beta : Real}
  {n : Nat}
-- given
  (M : Real -> Real)
  (henergy : 2 * (M beta) ^ 2 * (((2 * n + 1 : Nat) : Real) ^ 2) <= fvMeanNegEnergy (plusField 3) n (bondFinsetTouch 3 n) beta 0 - fvMeanNegEnergy (interfaceField (⟨2, by omega⟩ : Fin 3)) n (bondFinsetTouch 3 n) beta 0) :
-- imply
  2 * (M beta) ^ 2 <= deriv (fun b => standardCubicInterfaceDensity b n) beta := by
-- proof
  apply StatMech.FrontierA.standardCubicInterfaceDensity_deriv_ge_two_mul_sq_of_energyDeficit M beta n henergy

/--
[standardCubicInterfaceDensity_deriv_ge_two_mul_magnetization_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionLebowitzPfisterLower.lean)
-/
@[path]
private lemma standardCubicInterfaceDensity_deriv_ge_two_mul_magnetization_sq_eq
  {beta : Real}
  {n : Nat}
-- given
  (hbeta : 0 <= beta)
  (hn : 0 < n) :
-- imply
  2 * magnetization 3 beta ^ 2 <= deriv (fun b => standardCubicInterfaceDensity b n) beta := by
-- proof
  apply StatMech.FrontierA.standardCubicInterfaceDensity_deriv_ge_two_mul_magnetization_sq beta hbeta n hn

/--
[standardCubicInterfaceDensity_hasWeakLowerBound_of_energyDeficit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionLebowitzPfisterLower.lean)
-/
@[path]
private lemma standardCubicInterfaceDensity_hasWeakLowerBound_of_energyDeficit_eq
  {n : Nat}
-- given
  (M : Real -> Real)
  (hMnonneg : forall beta, 0 < beta -> 0 <= M beta)
  (hMmono : MonotoneOn M (Ioi 0))
  (henergy : forall beta, 0 < beta -> 2 * (M beta) ^ 2 * (((2 * n + 1 : Nat) : Real) ^ 2) <= fvMeanNegEnergy (plusField 3) n (bondFinsetTouch 3 n) beta 0 - fvMeanNegEnergy (interfaceField (⟨2, by omega⟩ : Fin 3)) n (bondFinsetTouch 3 n) beta 0) :
-- imply
  HasWeakSurfaceTensionLowerBound 1 M (fun beta => standardCubicInterfaceDensity beta n) := by
-- proof
  apply StatMech.FrontierA.standardCubicInterfaceDensity_hasWeakLowerBound_of_energyDeficit M hMnonneg hMmono n henergy

/--
[rectangularIsingSurfaceTension_pos_iff_ordered_of_finite_energy_deficit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionLebowitzPfisterLower.lean)
-/
@[path]
private lemma rectangularIsingSurfaceTension_pos_iff_ordered_of_finite_energy_deficit_eq
  {betaC : Real}
-- given
  (hregime : HasOrderedMagnetizationRegime (magnetization 3) betaC)
  (hMnonneg : forall beta, 0 < beta -> 0 <= magnetization 3 beta)
  (hMmono : MonotoneOn (magnetization 3) (Ioi 0))
  (hprism : forall beta, 0 < beta -> HasPrismCubicalSurfaceComparison beta)
  (hupper : forall n beta, 0 < beta -> standardCubicInterfaceDensity beta n <= 2 * beta * (magnetization 3 beta) ^ 2)
  (henergy : forall n beta, 0 < beta -> 2 * (magnetization 3 beta) ^ 2 * (((2 * n + 1 : Nat) : Real) ^ 2) <= fvMeanNegEnergy (plusField 3) n (bondFinsetTouch 3 n) beta 0 - fvMeanNegEnergy (interfaceField (⟨2, by omega⟩ : Fin 3)) n (bondFinsetTouch 3 n) beta 0) :
-- imply
  forall beta, 0 < beta -> (0 < rectangularIsingSurfaceTension beta <-> betaC < beta) := by
-- proof
  apply StatMech.FrontierA.rectangularIsingSurfaceTension_pos_iff_ordered_of_finite_energy_deficit hregime hMnonneg hMmono hprism hupper henergy


-- created on 2026-10-23
