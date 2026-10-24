import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionCubicalPrismEnergy
open StatMech StatMech.FrontierA


/--
[oddCubicalCellEquivPrismSite_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCubicalPrismEnergy.lean)
-/
@[path]
private lemma oddCubicalCellEquivPrismSite_symm_apply_eq
  {n : Nat}
  {v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n} :
-- imply
  (oddCubicalCellEquivPrismSite n).symm v = ⟨v.x, v.y, v.z⟩ := by
-- proof
  apply StatMech.FrontierA.oddCubicalCellEquivPrismSite_symm_apply n v

/--
[cubicalPlaquetteToOddPrism_leftInverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCubicalPrismEnergy.lean)
-/
@[path]
private lemma cubicalPlaquetteToOddPrism_leftInverse_eq
  {n : Nat} :
-- imply
  Function.LeftInverse (oddPrismToCubicalPlaquette n) (cubicalPlaquetteToOddPrism n) := by
-- proof
  apply StatMech.FrontierA.cubicalPlaquetteToOddPrism_leftInverse n

/--
[cubicalPlaquetteToOddPrism_rightInverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCubicalPrismEnergy.lean)
-/
@[path]
private lemma cubicalPlaquetteToOddPrism_rightInverse_eq
  {n : Nat} :
-- imply
  Function.RightInverse (oddPrismToCubicalPlaquette n) (cubicalPlaquetteToOddPrism n) := by
-- proof
  apply StatMech.FrontierA.cubicalPlaquetteToOddPrism_rightInverse n

/--
[finBackward_oddInternalFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCubicalPrismEnergy.lean)
-/
@[path]
private lemma finBackward_oddInternalFace_eq
  {n : Nat}
  {k : Fin (2 * n)} :
-- imply
  finBackward (⟨k.val + 1, by omega⟩ : Fin (2 * n + 2)) = some (⟨k.val, by omega⟩ : Fin (2 * n + 1)) := by
-- proof
  apply StatMech.FrontierA.finBackward_oddInternalFace n k

/--
[finForward_oddInternalFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCubicalPrismEnergy.lean)
-/
@[path]
private lemma finForward_oddInternalFace_eq
  {n : Nat}
  {k : Fin (2 * n)} :
-- imply
  finForward (⟨k.val + 1, by omega⟩ : Fin (2 * n + 2)) = some (⟨k.val + 1, by omega⟩ : Fin (2 * n + 1)) := by
-- proof
  apply StatMech.FrontierA.finForward_oddInternalFace n k

/--
[finBackward_oddZeroFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCubicalPrismEnergy.lean)
-/
@[path]
private lemma finBackward_oddZeroFace_eq
  {n : Nat} :
-- imply
  finBackward (0 : Fin (2 * n + 2)) = (none : Option (Fin (2 * n + 1))) := by
-- proof
  apply StatMech.FrontierA.finBackward_oddZeroFace n

/--
[finForward_oddZeroFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCubicalPrismEnergy.lean)
-/
@[path]
private lemma finForward_oddZeroFace_eq
  {n : Nat} :
-- imply
  finForward (0 : Fin (2 * n + 2)) = some (0 : Fin (2 * n + 1)) := by
-- proof
  apply StatMech.FrontierA.finForward_oddZeroFace n

/--
[finBackward_oddLastFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCubicalPrismEnergy.lean)
-/
@[path]
private lemma finBackward_oddLastFace_eq
  {n : Nat} :
-- imply
  finBackward (Fin.last (2 * n + 1) : Fin (2 * n + 2)) = some (Fin.last (2 * n) : Fin (2 * n + 1)) := by
-- proof
  apply StatMech.FrontierA.finBackward_oddLastFace n

/--
[finForward_oddLastFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCubicalPrismEnergy.lean)
-/
@[path]
private lemma finForward_oddLastFace_eq
  {n : Nat} :
-- imply
  finForward (Fin.last (2 * n + 1) : Fin (2 * n + 2)) = (none : Option (Fin (2 * n + 1))) := by
-- proof
  apply StatMech.FrontierA.finForward_oddLastFace n

/--
[boolAgreement_eq_spin_not_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCubicalPrismEnergy.lean)
-/
@[path]
private lemma boolAgreement_eq_spin_not_mul_eq
  {a b : Bool} :
-- imply
  (if a = b then (1 : Real) else -1) = (if !a then (1 : Real) else -1) * (if !b then (1 : Real) else -1) := by
-- proof
  apply StatMech.FrontierA.boolAgreement_eq_spin_not_mul a b

/--
[boolFalseAgreement_eq_spin_not](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCubicalPrismEnergy.lean)
-/
@[path]
private lemma boolFalseAgreement_eq_spin_not_eq
  {a : Bool} :
-- imply
  (if false = a then (1 : Real) else -1) = (if !a then (1 : Real) else -1) := by
-- proof
  apply StatMech.FrontierA.boolFalseAgreement_eq_spin_not a

/--
[boolAgreementFalse_eq_spin_not](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCubicalPrismEnergy.lean)
-/
@[path]
private lemma boolAgreementFalse_eq_spin_not_eq
  {a : Bool} :
-- imply
  (if a = false then (1 : Real) else -1) = (if !a then (1 : Real) else -1) := by
-- proof
  apply StatMech.FrontierA.boolAgreementFalse_eq_spin_not a

/--
[oddCubicalDualAgreement_eq_plusInteraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCubicalPrismEnergy.lean)
-/
@[path]
private lemma oddCubicalDualAgreement_eq_plusInteraction_eq
  {n : Nat}
  {s : AnchoredConfig (CubicalDualVertex (2 * n + 1) (2 * n + 1) (2 * n + 1)) none}
  {q : OddPrismTouchIndex n} :
-- imply
  (if s.1 (cubicalDualEnds (oddPrismToCubicalPlaquette n q)).1 = s.1 (cubicalDualEnds (oddPrismToCubicalPlaquette n q)).2 then (1 : Real) else -1) = oddPrismPlusInteractionTerm n (oddCubicalAnchoredEquivPrismConfig n s) q := by
-- proof
  apply StatMech.FrontierA.oddCubicalDualAgreement_eq_plusInteraction n s q

/--
[sum_oddCubicalDualAgreement_eq_plusPrismInteraction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCubicalPrismEnergy.lean)
-/
@[path]
private lemma sum_oddCubicalDualAgreement_eq_plusPrismInteraction_eq
  {J beta : Real}
  {n : Nat}
  {s : AnchoredConfig (CubicalDualVertex (2 * n + 1) (2 * n + 1) (2 * n + 1)) none} :
-- imply
  (∑ p : CubicalPlaquette (2 * n + 1) (2 * n + 1) (2 * n + 1), beta * J * (if s.1 (cubicalDualEnds p).1 = s.1 (cubicalDualEnds p).2 then (1 : Real) else -1)) = beta * J * (rectangularPrismInternalInteraction (oddCubicalAnchoredEquivPrismConfig n s) + rectangularPrismPlusBoundaryInteraction (oddCubicalAnchoredEquivPrismConfig n s)) := by
-- proof
  apply StatMech.FrontierA.sum_oddCubicalDualAgreement_eq_plusPrismInteraction J beta n s

/--
[oddCubicalDualPartition_eq_two_mul_plusPrismPartition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCubicalPrismEnergy.lean)
-/
@[path]
private lemma oddCubicalDualPartition_eq_two_mul_plusPrismPartition_eq
  {J beta : Real}
  {n : Nat} :
-- imply
  multibondIsingPartition (cubicalDualEnds (a := 2 * n + 1) (b := 2 * n + 1) (c := 2 * n + 1)) (fun _ : CubicalPlaquette (2 * n + 1) (2 * n + 1) (2 * n + 1) => beta * J) = 2 * rectangularPrismPlusPartition J beta (2 * n + 1) (2 * n + 1) n := by
-- proof
  apply StatMech.FrontierA.oddCubicalDualPartition_eq_two_mul_plusPrismPartition J beta n

/--
[sum_oddCubicalCentralSheet_eq_prismInterface](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCubicalPrismEnergy.lean)
-/
@[path]
private lemma sum_oddCubicalCentralSheet_eq_prismInterface_eq
  {J beta : Real}
  {n : Nat}
  {s : AnchoredConfig (CubicalDualVertex (2 * n + 1) (2 * n + 1) (2 * n + 1)) none}
-- given
  (hn : 0 < n) :
-- imply
  (∑ p ∈ cubicalXYSheet (a := 2 * n + 1) (b := 2 * n + 1) (c := 2 * n + 1) (⟨n + 1, by omega⟩ : Fin (2 * n + 2)), beta * J * (if s.1 (cubicalDualEnds p).1 = s.1 (cubicalDualEnds p).2 then (1 : Real) else -1)) = beta * J * rectangularPrismInterfaceInteraction (oddCubicalAnchoredEquivPrismConfig n s) := by
-- proof
  apply StatMech.FrontierA.sum_oddCubicalCentralSheet_eq_prismInterface J beta n hn s

/--
[sum_oddCubicalCentralTwist_eq_twistedPrismExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCubicalPrismEnergy.lean)
-/
@[path]
private lemma sum_oddCubicalCentralTwist_eq_twistedPrismExponent_eq
  {J beta : Real}
  {n : Nat}
  {s : AnchoredConfig (CubicalDualVertex (2 * n + 1) (2 * n + 1) (2 * n + 1)) none}
-- given
  (hn : 0 < n) :
-- imply
  (∑ p : CubicalPlaquette (2 * n + 1) (2 * n + 1) (2 * n + 1), multibondTwistCoupling (fun _ : CubicalPlaquette (2 * n + 1) (2 * n + 1) (2 * n + 1) => beta * J) (cubicalXYSheet (a := 2 * n + 1) (b := 2 * n + 1) (c := 2 * n + 1) (⟨n + 1, by omega⟩ : Fin (2 * n + 2))) p * (if s.1 (cubicalDualEnds p).1 = s.1 (cubicalDualEnds p).2 then (1 : Real) else -1)) = -beta * rectangularPrismTwistedEnergy J (oddCubicalAnchoredEquivPrismConfig n s) := by
-- proof
  apply StatMech.FrontierA.sum_oddCubicalCentralTwist_eq_twistedPrismExponent J beta n hn s

/--
[oddCubicalCentralTwistedPartition_eq_two_mul_twistedPrismPartition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCubicalPrismEnergy.lean)
-/
@[path]
private lemma oddCubicalCentralTwistedPartition_eq_two_mul_twistedPrismPartition_eq
  {J beta : Real}
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  multibondIsingPartition (cubicalDualEnds (a := 2 * n + 1) (b := 2 * n + 1) (c := 2 * n + 1)) (multibondTwistCoupling (fun _ : CubicalPlaquette (2 * n + 1) (2 * n + 1) (2 * n + 1) => beta * J) (cubicalXYSheet (a := 2 * n + 1) (b := 2 * n + 1) (c := 2 * n + 1) (⟨n + 1, by omega⟩ : Fin (2 * n + 2)))) = 2 * rectangularPrismTwistedPartition J beta (2 * n + 1) (2 * n + 1) n := by
-- proof
  apply StatMech.FrontierA.oddCubicalCentralTwistedPartition_eq_two_mul_twistedPrismPartition J beta n hn

/--
[oddCubicalCentralDisorderFreeEnergy_eq_prism](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCubicalPrismEnergy.lean)
-/
@[path]
private lemma oddCubicalCentralDisorderFreeEnergy_eq_prism_eq
  {J beta : Real}
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  multibondDisorderFreeEnergy (cubicalDualEnds (a := 2 * n + 1) (b := 2 * n + 1) (c := 2 * n + 1)) (fun _ : CubicalPlaquette (2 * n + 1) (2 * n + 1) (2 * n + 1) => beta * J) (cubicalXYSheet (a := 2 * n + 1) (b := 2 * n + 1) (c := 2 * n + 1) (⟨n + 1, by omega⟩ : Fin (2 * n + 2))) = StatMech.Ising.rectangularDobrushinFreeEnergy J beta (2 * n + 1) (2 * n + 1) n := by
-- proof
  apply StatMech.FrontierA.oddCubicalCentralDisorderFreeEnergy_eq_prism J beta n hn

/--
[centralCubicalIsingDisorderDensity_eq_rectangularPrismInterfaceDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCubicalPrismEnergy.lean)
-/
@[path]
private lemma centralCubicalIsingDisorderDensity_eq_rectangularPrismInterfaceDensity_eq
  {beta : Real}
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  centralCubicalIsingDisorderDensity beta n = rectangularPrismInterfaceDensity beta n := by
-- proof
  apply StatMech.FrontierA.centralCubicalIsingDisorderDensity_eq_rectangularPrismInterfaceDensity beta n hn

/--
[standardCubicInterfaceDensity_eq_centralCubicalIsingDisorderDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCubicalPrismEnergy.lean)
-/
@[path]
private lemma standardCubicInterfaceDensity_eq_centralCubicalIsingDisorderDensity_eq
  {beta : Real}
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  standardCubicInterfaceDensity beta n = centralCubicalIsingDisorderDensity beta n := by
-- proof
  apply StatMech.FrontierA.standardCubicInterfaceDensity_eq_centralCubicalIsingDisorderDensity beta n hn

/--
[hasPrismCubicalSurfaceComparison_iff_centralSheet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCubicalPrismEnergy.lean)
-/
@[path]
private lemma hasPrismCubicalSurfaceComparison_iff_centralSheet_eq
  {beta : Real} :
-- imply
  HasPrismCubicalSurfaceComparison beta ↔ Tendsto (fun n => centralCubicalIsingDisorderDensity beta n - oddCubicalIsingDisorderDensity beta n) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.hasPrismCubicalSurfaceComparison_iff_centralSheet beta

/--
[hasPrismCubicalSurfaceComparison_iff_standardSheet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCubicalPrismEnergy.lean)
-/
@[path]
private lemma hasPrismCubicalSurfaceComparison_iff_standardSheet_eq
  {beta : Real} :
-- imply
  HasPrismCubicalSurfaceComparison beta ↔ Tendsto (fun n => standardCubicInterfaceDensity beta n - oddCubicalIsingDisorderDensity beta n) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierA.hasPrismCubicalSurfaceComparison_iff_standardSheet beta

/--
[standardCubicInterfaceDensity_tendsto_of_prismComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCubicalPrismEnergy.lean)
-/
@[path]
private lemma standardCubicInterfaceDensity_tendsto_of_prismComparison_eq
  {beta : Real}
-- given
  (hbeta : 0 < beta)
  (hprism : HasPrismCubicalSurfaceComparison beta) :
-- imply
  Tendsto (standardCubicInterfaceDensity beta) atTop (nhds (rectangularIsingSurfaceTension beta)) := by
-- proof
  apply StatMech.FrontierA.standardCubicInterfaceDensity_tendsto_of_prismComparison hbeta hprism

/--
[rectangularIsingSurfaceTension_pos_iff_ordered_of_prismComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionCubicalPrismEnergy.lean)
-/
@[path]
private lemma rectangularIsingSurfaceTension_pos_iff_ordered_of_prismComparison_eq
  {betaC : Real}
-- given
  (hregime : StatMech.Ising.HasOrderedMagnetizationRegime (StatMech.Ising.magnetization 3) betaC)
  (hprism : forall beta, 0 < beta -> HasPrismCubicalSurfaceComparison beta)
  (hupper : forall n beta, 0 < beta -> standardCubicInterfaceDensity beta n <= 2 * beta * (StatMech.Ising.magnetization 3 beta) ^ 2)
  (hweak : forall n, StatMech.Ising.HasWeakSurfaceTensionLowerBound 1 (StatMech.Ising.magnetization 3) (fun beta => standardCubicInterfaceDensity beta n)) :
-- imply
  forall beta, 0 < beta -> (0 < rectangularIsingSurfaceTension beta <-> betaC < beta) := by
-- proof
  apply StatMech.FrontierA.rectangularIsingSurfaceTension_pos_iff_ordered_of_prismComparison hregime hprism hupper hweak


-- created on 2026-10-23
