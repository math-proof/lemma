import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveMixedNoLoop
open StatMech StatMech.FrontierD


/--
[fkRectCritical_zeroTurnAbove_le_half_of_mixedAdaptiveTail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveMixedNoLoop.lean)
-/
@[path]
private lemma fkRectCritical_zeroTurnAbove_le_half_of_mixedAdaptiveTail_eq
  {R : FKRectTorus}
  {q : Real}
  {n : Nat}
-- given
  (hq : 1 ≤ q)
  (hinj : ∀ omega : R.Configuration, fkRectZeroTurnCutRemainderCount R omega ≤ 2 * fkRectRawHorizontalCrossingClusterCount R (fkRectForceCutClosed R omega) + 2)
  (hsmall : Nat.choose R.height (n + 1) * ((FK.freeInfiniteVolume 2 (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq)) (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq)) (zero_lt_one.trans_le hq) : MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))).real (FK.boxBdryConnEvent 2 (R.width - 2))) ^ (n + 1) ≤ FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) / 2) :
-- imply
  fkRectCriticalZeroTurnAboveMass R q (2 * R.width + 2 * n + 2) ≤ (1 : Real) / 2 := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_zeroTurnAbove_le_half_of_mixedAdaptiveTail R hq hinj n hsmall

/--
[fkRectCritical_zeroTurnAbove_le_half_of_mixedAnnulusCharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveMixedNoLoop.lean)
-/
@[path]
private lemma fkRectCritical_zeroTurnAbove_le_half_of_mixedAnnulusCharge_eq
  {R : FKRectTorus}
  {q : Real}
  {n : Nat}
-- given
  (hq : 1 ≤ q)
  (charge : ∀ omega : R.Configuration, FKRectZeroTurnMixedAnnulusCharge R omega)
  (hsmall : Nat.choose R.height (n + 1) * ((FK.freeInfiniteVolume 2 (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq)) (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq)) (zero_lt_one.trans_le hq) : MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))).real (FK.boxBdryConnEvent 2 (R.width - 2))) ^ (n + 1) ≤ FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) / 2) :
-- imply
  fkRectCriticalZeroTurnAboveMass R q (2 * R.width + 2 * n + 2) ≤ (1 : Real) / 2 := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_zeroTurnAbove_le_half_of_mixedAnnulusCharge R hq charge n hsmall

/--
[zeroTurnCost_div_two_q_le_allSectorNormalization_of_mixedAnnulusCharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveMixedNoLoop.lean)
-/
@[path]
private lemma zeroTurnCost_div_two_q_le_allSectorNormalization_of_mixedAnnulusCharge_eq
  {R : FKRectTorus}
  {q : Real}
  {n : Nat}
-- given
  (hq : 4 < q)
  (charge : ∀ omega : R.Configuration, FKRectZeroTurnMixedAnnulusCharge R omega)
  (hsmall : Nat.choose R.height (n + 1) * ((FK.freeInfiniteVolume 2 (fkRectCriticalP_pos (by linarith : 0 < q)) (fkRectCriticalP_lt_one (by linarith : 0 < q)) (by linarith : 0 < q) : MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))).real (FK.boxBdryConnEvent 2 (R.width - 2))) ^ (n + 1) ≤ FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) / 2) :
-- imply
  (2 / Real.sqrt q) ^ (2 * R.width + 2 * n + 2) / (2 * q) ≤ fkRectAllSectorNormalization R q := by
-- proof
  apply StatMech.FrontierD.zeroTurnCost_div_two_q_le_allSectorNormalization_of_mixedAnnulusCharge R hq charge n hsmall

/--
[fkRectCritical_zeroTurnAbove_le_half_of_mixedTouchedCrossings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveMixedNoLoop.lean)
-/
@[path]
private lemma fkRectCritical_zeroTurnAbove_le_half_of_mixedTouchedCrossings_eq
  {R : FKRectTorus}
  {q : Real}
  {n : Nat}
-- given
  (hq : 1 ≤ q)
  (certificate : ∀ omega : R.Configuration, FKRectZeroTurnMixedTouchedCertificate R omega)
  (hsmall : Nat.choose R.height (n + 1) * ((FK.freeInfiniteVolume 2 (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq)) (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq)) (zero_lt_one.trans_le hq) : MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))).real (FK.boxBdryConnEvent 2 (R.width - 2))) ^ (n + 1) ≤ FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) / 2) :
-- imply
  fkRectCriticalZeroTurnAboveMass R q (2 * R.width + 2 * n + 2) ≤ (1 : Real) / 2 := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_zeroTurnAbove_le_half_of_mixedTouchedCrossings R hq certificate n hsmall

/--
[zeroTurnCost_div_two_q_le_allSectorNormalization_of_mixedTouchedCrossings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveMixedNoLoop.lean)
-/
@[path]
private lemma zeroTurnCost_div_two_q_le_allSectorNormalization_of_mixedTouchedCrossings_eq
  {R : FKRectTorus}
  {q : Real}
  {n : Nat}
-- given
  (hq : 4 < q)
  (certificate : ∀ omega : R.Configuration, FKRectZeroTurnMixedTouchedCertificate R omega)
  (hsmall : Nat.choose R.height (n + 1) * ((FK.freeInfiniteVolume 2 (fkRectCriticalP_pos (by linarith : 0 < q)) (fkRectCriticalP_lt_one (by linarith : 0 < q)) (by linarith : 0 < q) : MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))).real (FK.boxBdryConnEvent 2 (R.width - 2))) ^ (n + 1) ≤ FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) / 2) :
-- imply
  (2 / Real.sqrt q) ^ (2 * R.width + 2 * n + 2) / (2 * q) ≤ fkRectAllSectorNormalization R q := by
-- proof
  apply StatMech.FrontierD.zeroTurnCost_div_two_q_le_allSectorNormalization_of_mixedTouchedCrossings R hq certificate n hsmall


-- created on 2026-10-23
