import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWindingTailPrescribedCylinderTransfer.Part4
open Finset StatMech StatMech.FrontierD


/--
[fkRectForceLocalPattern_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingTailPrescribedCylinderTransfer.lean)
-/
@[path]
private lemma fkRectForceLocalPattern_of_mem_eq
  {R : FKRectTorus}
  {I : Finset R.EdgeIndex}
  {eta : FKRectLocalPattern R I}
  {omega : R.Configuration}
  {a : R.EdgeIndex}
-- given
  (ha : a ∈ I) :
-- imply
  fkRectForceLocalPattern R I eta omega a = eta ⟨a, ha⟩ := by
-- proof
  apply StatMech.FrontierD.fkRectForceLocalPattern_of_mem R eta omega ha

/--
[fkRectForceLocalPattern_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingTailPrescribedCylinderTransfer.lean)
-/
@[path]
private lemma fkRectForceLocalPattern_of_not_mem_eq
  {R : FKRectTorus}
  {I : Finset R.EdgeIndex}
  {eta : FKRectLocalPattern R I}
  {omega : R.Configuration}
  {a : R.EdgeIndex}
-- given
  (ha : a ∉ I) :
-- imply
  fkRectForceLocalPattern R I eta omega a = omega a := by
-- proof
  apply StatMech.FrontierD.fkRectForceLocalPattern_of_not_mem R eta omega ha

/--
[fkRectCritical_cFE_pow_mul_forceLocalPattern_preimage_le_event](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingTailPrescribedCylinderTransfer.lean)
-/
@[path]
private lemma fkRectCritical_cFE_pow_mul_forceLocalPattern_preimage_le_event_eq
  {R : FKRectTorus}
  {q : Real}
  {I : Finset R.EdgeIndex}
  {eta : FKRectLocalPattern R I}
  {A : Set R.Configuration}
-- given
  (hq : 1 ≤ q) :
-- imply
  FK.cFE (fkRectCriticalP q) q ^ I.card * fkRectCriticalEventMass R q (fkRectForceLocalPattern R I eta ⁻¹' A) ≤ fkRectCriticalEventMass R q A := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_cFE_pow_mul_forceLocalPattern_preimage_le_event R hq I eta A

/--
[fkRectCritical_cFE_pow_mul_event_le_two_pow_mul_of_localRepair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingTailPrescribedCylinderTransfer.lean)
-/
@[path]
private lemma fkRectCritical_cFE_pow_mul_event_le_two_pow_mul_of_localRepair_eq
  {R : FKRectTorus}
  {q : Real}
  {I : Finset R.EdgeIndex}
  {Source Target : Set R.Configuration}
-- given
  (hq : 1 ≤ q)
  (hrepair : ∀ omega, omega ∈ Source → ∃ eta : FKRectLocalPattern R I, fkRectForceLocalPattern R I eta omega ∈ Target) :
-- imply
  FK.cFE (fkRectCriticalP q) q ^ I.card * fkRectCriticalEventMass R q Source ≤ (2 ^ I.card : Nat) * fkRectCriticalEventMass R q Target := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_cFE_pow_mul_event_le_two_pow_mul_of_localRepair R hq I Source Target hrepair

/--
[fkRectCriticalWindingTailMass_eq_eventMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingTailPrescribedCylinderTransfer.lean)
-/
@[path]
private lemma fkRectCriticalWindingTailMass_eq_eventMass_eq
  {R : FKRectTorus}
  {q : Real}
  {r : Nat} :
-- imply
  fkRectCriticalWindingTailMass R q r = fkRectCriticalEventMass R q {omega | r ≤ fkRectUnorientedVerticalWindingNumber R omega} := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalWindingTailMass_eq_eventMass R q r

/--
[fkRectCriticalWindingTailMass_cFE_pow_le_prescribedCylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingTailPrescribedCylinderTransfer.lean)
-/
@[path]
private lemma fkRectCriticalWindingTailMass_cFE_pow_le_prescribedCylinder_eq
  {R : FKRectTorus}
  {q : Real}
  {r : Nat}
  {I : Finset R.EdgeIndex}
  {pair : Fin R.width → Fin R.width}
  {S : Finset (Fin R.width)}
-- given
  (hq : 1 ≤ q)
  (hrepair : FKRectWindingTailPrescribedCylinderRepair R r I pair S) :
-- imply
  FK.cFE (fkRectCriticalP q) q ^ I.card * fkRectCriticalWindingTailMass R q r ≤ (2 ^ I.card : Nat) * StatMech.Probability.finiteEventMass (FK.fkProb (fkRectHorizontalCylinderGraph R) (fkRectCriticalP q) q) {rho | FKRectHorizontalCylinderDistinctPairedWitness R pair S rho} := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalWindingTailMass_cFE_pow_le_prescribedCylinder R hq r I pair S hrepair

/--
[fkRectCriticalWindingTailMass_cFE_perimeter_le_prescribedCylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingTailPrescribedCylinderTransfer.lean)
-/
@[path]
private lemma fkRectCriticalWindingTailMass_cFE_perimeter_le_prescribedCylinder_eq
  {R : FKRectTorus}
  {q : Real}
  {r perimeter : Nat}
  {I : Finset R.EdgeIndex}
  {pair : Fin R.width → Fin R.width}
  {S : Finset (Fin R.width)}
-- given
  (hq : 1 ≤ q)
  (hI : I.card ≤ perimeter)
  (hrepair : FKRectWindingTailPrescribedCylinderRepair R r I pair S) :
-- imply
  FK.cFE (fkRectCriticalP q) q ^ perimeter * fkRectCriticalWindingTailMass R q r ≤ (2 ^ perimeter : Nat) * StatMech.Probability.finiteEventMass (FK.fkProb (fkRectHorizontalCylinderGraph R) (fkRectCriticalP q) q) {rho | FKRectHorizontalCylinderDistinctPairedWitness R pair S rho} := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalWindingTailMass_cFE_perimeter_le_prescribedCylinder R hq r perimeter I pair S hI hrepair

/--
[card_fkRectAfBottomIndexSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingTailPrescribedCylinderTransfer.lean)
-/
@[path]
private lemma card_fkRectAfBottomIndexSet_eq
  {R : FKRectTorus}
  {r : Nat}
-- given
  (hwidth : 2 * r ≤ R.width) :
-- imply
  (fkRectAfBottomIndexSet R r).card = r := by
-- proof
  apply StatMech.FrontierD.card_fkRectAfBottomIndexSet R r hwidth

/--
[fkRectAfWindingTailPrescribedCylinderRepair_of_sourceWidth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingTailPrescribedCylinderTransfer.lean)
-/
@[path]
private lemma fkRectAfWindingTailPrescribedCylinderRepair_of_sourceWidth_eq
  {R : FKRectTorus}
  {r : Nat}
  {I : Finset R.EdgeIndex}
-- given
  (hwidth : 2 * r ≤ R.width)
  (hrepair : FKRectWindingTailPrescribedCylinderRepair R r I (fkRectAfPair R) (fkRectAfBottomIndexSet R r)) :
-- imply
  FKRectAfWindingTailPrescribedCylinderRepair R r I := by
-- proof
  apply StatMech.FrontierD.fkRectAfWindingTailPrescribedCylinderRepair_of_sourceWidth R r I hwidth hrepair

/--
[fkRectCriticalWindingTailMass_cFE_perimeter_le_afCylinderEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWindingTailPrescribedCylinderTransfer.lean)
-/
@[path]
private lemma fkRectCriticalWindingTailMass_cFE_perimeter_le_afCylinderEvent_eq
  {R : FKRectTorus}
  {q : Real}
  {r perimeter : Nat}
  {I : Finset R.EdgeIndex}
-- given
  (hq : 1 ≤ q)
  (hI : I.card ≤ perimeter)
  (hrepair : FKRectAfWindingTailPrescribedCylinderRepair R r I) :
-- imply
  FK.cFE (fkRectCriticalP q) q ^ perimeter * fkRectCriticalWindingTailMass R q r ≤ (2 ^ perimeter : Nat) * StatMech.Probability.finiteEventMass (FK.fkProb (fkRectHorizontalCylinderGraph R) (fkRectCriticalP q) q) {rho | FKRectHorizontalCylinderDistinctPairedWitness R (fkRectAfPair R) (fkRectAfBottomIndexSet R r) rho} := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalWindingTailMass_cFE_perimeter_le_afCylinderEvent R hq r perimeter I hI hrepair


-- created on 2026-10-23
