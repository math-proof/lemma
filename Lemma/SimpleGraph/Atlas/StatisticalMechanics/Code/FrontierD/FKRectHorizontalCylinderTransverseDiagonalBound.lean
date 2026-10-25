import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderTransverseDiagonalBound
open MeasureTheory SimpleGraph StatMech.Lattice StatMech StatMech.FrontierD


/--
[fkQgt4CriticalFree_ofPairedWitness_embedding_le_sqrt_exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTransverseDiagonalBound.lean)
-/
@[path]
private lemma fkQgt4CriticalFree_ofPairedWitness_embedding_le_sqrt_exact_eq
  {q : Real}
  {R : FKRectTorus}
  {T : Finset (Fin R.width)}
  {psi : ConfigSpace (Sym2 R.Vertex)}
  {x : Fin R.width}
-- given
  (hq : 4 < q)
  (pair : Fin R.width -> Fin R.width)
  (hT : T.Nonempty)
  (hbase : FKRectHorizontalCylinderDistinctPairedWitness R pair T psi)
  (hsource : ¬ FKRectHorizontalCylinderExploredVertex R psi T (x, fkRectBottomRow R))
  (htarget : ¬ FKRectHorizontalCylinderExploredVertex R psi T (pair x, fkRectTopRow R)) :
-- imply
  FK.infiniteTwoPointReal (fkQgt4CriticalFreeMeasure hq : Measure (ConfigSpace (Sym2 (Site 2)))) ((FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness R psi pair T hT hbase).embedding ⟨(x, fkRectBottomRow R), hsource⟩).1 ((FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness R psi pair T hT hbase).embedding ⟨(pair x, fkRectTopRow R), htarget⟩).1 <= Real.sqrt (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (R.height - 1)) := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFree_ofPairedWitness_embedding_le_sqrt_exact hq R pair T hT psi hbase x hsource htarget

/--
[fkRectHorizontalCylinderDistinctPairedWitness_mass_le_sqrtExact_pow_erase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTransverseDiagonalBound.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderDistinctPairedWitness_mass_le_sqrtExact_pow_erase_eq
  {q : Real}
  {R : FKRectTorus}
  {S : Finset (Fin R.width)}
  {first : Fin R.width}
-- given
  (hq : 4 < q)
  (pair : Fin R.width -> Fin R.width)
  (hfirst : first ∈ S) :
-- imply
  StatMech.Probability.finiteEventMass (FK.fkProb (fkRectHorizontalCylinderGraph R) (fkRectCriticalP q) q) {rho | FKRectHorizontalCylinderDistinctPairedWitness R pair S rho} <= Real.sqrt (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (R.height - 1)) ^ (S.erase first).card := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderDistinctPairedWitness_mass_le_sqrtExact_pow_erase hq R pair S first hfirst

/--
[fkRectAfCylinderEvent_mass_le_sqrtExact_pow_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTransverseDiagonalBound.lean)
-/
@[path]
private lemma fkRectAfCylinderEvent_mass_le_sqrtExact_pow_pred_eq
  {q : Real}
  {R : FKRectTorus}
  {r : Nat}
  {I : Finset R.EdgeIndex}
-- given
  (hq : 4 < q)
  (hr : 0 < r)
  (hrepair : FKRectAfWindingTailPrescribedCylinderRepair R r I) :
-- imply
  StatMech.Probability.finiteEventMass (FK.fkProb (fkRectHorizontalCylinderGraph R) (fkRectCriticalP q) q) {rho | FKRectHorizontalCylinderDistinctPairedWitness R (fkRectAfPair R) (fkRectAfBottomIndexSet R r) rho} <= Real.sqrt (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (R.height - 1)) ^ (r - 1) := by
-- proof
  apply StatMech.FrontierD.fkRectAfCylinderEvent_mass_le_sqrtExact_pow_pred hq R r hr hrepair

/--
[fkRectCriticalWindingTailMass_cFE_le_twoPow_mul_sqrtExact_pow_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTransverseDiagonalBound.lean)
-/
@[path]
private lemma fkRectCriticalWindingTailMass_cFE_le_twoPow_mul_sqrtExact_pow_pred_eq
  {q : Real}
  {R : FKRectTorus}
  {r perimeter : Nat}
  {I : Finset R.EdgeIndex}
-- given
  (hq : 4 < q)
  (hr : 0 < r)
  (hI : I.card <= perimeter)
  (hrepair : FKRectAfWindingTailPrescribedCylinderRepair R r I) :
-- imply
  FK.cFE (fkRectCriticalP q) q ^ perimeter * fkRectCriticalWindingTailMass R q r <= (2 ^ perimeter : Nat) * (Real.sqrt (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (R.height - 1))) ^ (r - 1) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalWindingTailMass_cFE_le_twoPow_mul_sqrtExact_pow_pred hq R r perimeter hr I hI hrepair


-- created on 2026-10-23
