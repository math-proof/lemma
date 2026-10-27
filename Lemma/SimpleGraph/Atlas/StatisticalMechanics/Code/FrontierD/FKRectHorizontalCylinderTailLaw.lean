import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderTailLaw
open StatMech StatMech.FrontierD


/--
[fkRectHorizontalCylinderCrossingClusterCount_congr_openSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTailLaw.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderCrossingClusterCount_congr_openSub_eq
  {R : FKRectTorus}
  {rho sigma : ConfigSpace (Sym2 R.Vertex)}
-- given
  (hgraph : FK.openSub (fkRectHorizontalCylinderGraph R) rho = FK.openSub (fkRectHorizontalCylinderGraph R) sigma) :
-- imply
  fkRectHorizontalCylinderCrossingClusterCount R rho = fkRectHorizontalCylinderCrossingClusterCount R sigma := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderCrossingClusterCount_congr_openSub R hgraph

/--
[fkRectHorizontalCylinderCrossingTail_edgeEvent_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTailLaw.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderCrossingTail_edgeEvent_eq_eq
  {R : FKRectTorus}
  {n : Nat} :
-- imply
  FK.ecz_closeOff (fkRectHorizontalCylinderGraph R) ⁻¹' fkRectHorizontalCylinderEdgeEvent R {eta | n <= fkRectHorizontalCutPrimalCrossingClusterCount R (fkRectForceHorizontalCutClosed R eta)} = {rho | n <= fkRectHorizontalCylinderCrossingClusterCount R rho} := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderCrossingTail_edgeEvent_eq R n

/--
[fkRectCriticalHorizontalCut_crossingTail_eq_finiteEventMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTailLaw.lean)
-/
@[path]
private lemma fkRectCriticalHorizontalCut_crossingTail_eq_finiteEventMass_eq
  {R : FKRectTorus}
  {q : Real}
  {n : Nat}
-- given
  (hq : 1 <= q) :
-- imply
  fkRectCriticalHorizontalCutEventMass R q {eta | n <= fkRectHorizontalCutPrimalCrossingClusterCount R (fkRectForceHorizontalCutClosed R eta)} = StatMech.Probability.finiteEventMass (FK.fkProb (fkRectHorizontalCylinderGraph R) (fkRectCriticalP q) q) {rho | n <= fkRectHorizontalCylinderCrossingClusterCount R rho} := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalHorizontalCut_crossingTail_eq_finiteEventMass R hq n

/--
[fkRectCriticalHorizontalCut_crossingTail_le_pow_pred_of_twoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderTailLaw.lean)
-/
@[path]
private lemma fkRectCriticalHorizontalCut_crossingTail_le_pow_pred_of_twoPoint_eq
  {R : FKRectTorus}
  {q a : Real}
  {n : Nat}
-- given
  (hq : 1 <= q)
  (ha : 0 <= a)
  (htwo : forall (pair : Fin R.width -> Fin R.width) (T : Finset (Fin R.width)) (hT : T.Nonempty) (x : Fin R.width) (hx : x ∉ T) (psi : ConfigSpace (Sym2 R.Vertex)) (hbase : FKRectHorizontalCylinderDistinctPairedWitness R pair T psi) (hsource : ¬ FKRectHorizontalCylinderExploredVertex R psi T (x, fkRectBottomRow R)) (htarget : ¬ FKRectHorizontalCylinderExploredVertex R psi T (pair x, fkRectTopRow R)), FK.infiniteTwoPointReal (FK.freeInfiniteVolume 2 (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq)) (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq)) (zero_lt_one.trans_le hq) : MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))) ((FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness R psi pair T hT hbase).embedding ⟨(x, fkRectBottomRow R), hsource⟩).1 ((FKRectHorizontalCylinderUnexploredPlanarization.ofPairedWitness R psi pair T hT hbase).embedding ⟨(pair x, fkRectTopRow R), htarget⟩).1 <= a)
  (hn : 0 < n) :
-- imply
  fkRectCriticalHorizontalCutEventMass R q {eta | n <= fkRectHorizontalCutPrimalCrossingClusterCount R (fkRectForceHorizontalCutClosed R eta)} <= Nat.choose R.width n * R.width ^ R.width * a ^ (n - 1) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalHorizontalCut_crossingTail_le_pow_pred_of_twoPoint R hq ha htwo n hn


-- created on 2026-10-23
