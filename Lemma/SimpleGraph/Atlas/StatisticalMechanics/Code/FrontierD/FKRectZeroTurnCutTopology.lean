import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnCutTopology.Part4
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectMedialLoopCanonicalVerticalFlux_eq_zero_of_not_hitsHorizontalSeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnCutTopology.lean)
-/
@[path]
private lemma fkRectMedialLoopCanonicalVerticalFlux_eq_zero_of_not_hitsHorizontalSeam_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKMedialLoop R.medialTorus (fkRectConfigurationToMedialPairing R omega)}
-- given
  (havoid : ¬ FKRectMedialHitsHorizontalSeam R omega C) :
-- imply
  fkMedialLoopCanonicalVerticalFlux (fkRectConfigurationToMedialPairing R omega) C = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectMedialLoopCanonicalVerticalFlux_eq_zero_of_not_hitsHorizontalSeam R omega C havoid

/--
[mem_fkRectMedialHorizontalSeamComponents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnCutTopology.lean)
-/
@[path]
private lemma mem_fkRectMedialHorizontalSeamComponents_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKMedialLoop R.medialTorus (fkRectConfigurationToMedialPairing R omega)} :
-- imply
  C ∈ fkRectMedialHorizontalSeamComponents R omega ↔ FKRectMedialHitsHorizontalSeam R omega C := by
-- proof
  apply StatMech.FrontierD.mem_fkRectMedialHorizontalSeamComponents R omega C

/--
[fkRectMedialHorizontalSeamComponents_card_le_two_width](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnCutTopology.lean)
-/
@[path]
private lemma fkRectMedialHorizontalSeamComponents_card_le_two_width_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  (fkRectMedialHorizontalSeamComponents R omega).card ≤ 2 * R.width := by
-- proof
  apply StatMech.FrontierD.fkRectMedialHorizontalSeamComponents_card_le_two_width R omega

/--
[mem_fkRectZeroTurnCutRemainderComponents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnCutTopology.lean)
-/
@[path]
private lemma mem_fkRectZeroTurnCutRemainderComponents_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {C : FKMedialLoop R.medialTorus (fkRectConfigurationToMedialPairing R omega)} :
-- imply
  C ∈ fkRectZeroTurnCutRemainderComponents R omega ↔ FKMedialTurningFiber.canonicalComponentTurn (fkRectConfigurationToMedialPairing R omega) C = 0 ∧ ¬ FKRectMedialHitsHorizontalSeam R omega C := by
-- proof
  apply StatMech.FrontierD.mem_fkRectZeroTurnCutRemainderComponents R omega C

/--
[fkRectZeroTurnLoopCount_le_seam_add_cutRemainder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnCutTopology.lean)
-/
@[path]
private lemma fkRectZeroTurnLoopCount_le_seam_add_cutRemainder_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectZeroTurnLoopCount R omega ≤ (fkRectMedialHorizontalSeamComponents R omega).card + fkRectZeroTurnCutRemainderCount R omega := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnLoopCount_le_seam_add_cutRemainder R omega

/--
[fkRectZeroTurnLoopCount_le_two_width_add_cutRemainder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnCutTopology.lean)
-/
@[path]
private lemma fkRectZeroTurnLoopCount_le_two_width_add_cutRemainder_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectZeroTurnLoopCount R omega ≤ 2 * R.width + fkRectZeroTurnCutRemainderCount R omega := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnLoopCount_le_two_width_add_cutRemainder R omega

/--
[fkRectZeroTurnLoopCount_le_two_width_add_primalDualCrossings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnCutTopology.lean)
-/
@[path]
private lemma fkRectZeroTurnLoopCount_le_two_width_add_primalDualCrossings_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
-- given
  (hinj : fkRectZeroTurnCutRemainderCount R omega ≤ fkRectRawPrimalDualHorizontalCrossingClusterCount R (fkRectForceCutClosed R omega)) :
-- imply
  fkRectZeroTurnLoopCount R omega ≤ 2 * R.width + fkRectPrimalDualHorizontalCrossingClusterCount R omega := by
-- proof
  apply StatMech.FrontierD.fkRectZeroTurnLoopCount_le_two_width_add_primalDualCrossings R omega hinj

/--
[fkRectCritical_zeroTurnAbove_le_primalDualCrossings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnCutTopology.lean)
-/
@[path]
private lemma fkRectCritical_zeroTurnAbove_le_primalDualCrossings_eq
  {R : FKRectTorus}
  {q : Real}
  {n : Nat}
-- given
  (hq : 1 ≤ q)
  (hinj : ∀ omega : R.Configuration, fkRectZeroTurnCutRemainderCount R omega ≤ fkRectRawPrimalDualHorizontalCrossingClusterCount R (fkRectForceCutClosed R omega)) :
-- imply
  FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) * fkRectCriticalZeroTurnAboveMass R q (2 * R.width + n) ≤ fkRectCriticalEventMass R q {eta | FKRectCutClosedConfiguration R eta ∧ n < fkRectPrimalDualHorizontalCrossingClusterCount R eta} := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_zeroTurnAbove_le_primalDualCrossings R hq hinj n

/--
[fkRectCritical_zeroTurnAbove_le_choose_mul_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnCutTopology.lean)
-/
@[path]
private lemma fkRectCritical_zeroTurnAbove_le_choose_mul_pow_eq
  {R : FKRectTorus}
  {q : Real}
  {n : Nat}
  {a : Real}
-- given
  (hq : 1 <= q)
  (hinj : forall omega : R.Configuration, fkRectZeroTurnCutRemainderCount R omega <= fkRectRawPrimalDualHorizontalCrossingClusterCount R (fkRectForceCutClosed R omega))
  (Witness : Finset (Fin (2 * R.height)) -> R.Configuration -> Prop)
  (hcover : forall eta : R.Configuration, FKRectCutClosedConfiguration R eta -> n < fkRectPrimalDualHorizontalCrossingClusterCount R eta -> exists S : Finset (Fin (2 * R.height)), S.card = n + 1 /\ Witness S eta)
  (hmass : forall S : Finset (Fin (2 * R.height)), S.card = n + 1 -> fkRectCriticalEventMass R q {eta | Witness S eta} <= a ^ (n + 1)) :
-- imply
  FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) * fkRectCriticalZeroTurnAboveMass R q (2 * R.width + n) <= Nat.choose (2 * R.height) (n + 1) * a ^ (n + 1) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_zeroTurnAbove_le_choose_mul_pow R hq hinj n a Witness hcover hmass

/--
[fkRectCritical_zeroTurnAbove_le_choose_mul_pow_of_sourceMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnCutTopology.lean)
-/
@[path]
private lemma fkRectCritical_zeroTurnAbove_le_choose_mul_pow_of_sourceMass_eq
  {R : FKRectTorus}
  {q : Real}
  {n : Nat}
  {a : Real}
-- given
  (hq : 1 <= q)
  (hinj : forall omega : R.Configuration, fkRectZeroTurnCutRemainderCount R omega <= fkRectRawPrimalDualHorizontalCrossingClusterCount R (fkRectForceCutClosed R omega))
  (hmass : forall S : Finset (Fin (2 * R.height)), S.card = n + 1 -> fkRectCriticalEventMass R q {eta | FKRectPrimalDualCrossingSourceWitness R S eta} <= a ^ (n + 1)) :
-- imply
  FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) * fkRectCriticalZeroTurnAboveMass R q (2 * R.width + n) <= Nat.choose (2 * R.height) (n + 1) * a ^ (n + 1) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_zeroTurnAbove_le_choose_mul_pow_of_sourceMass R hq hinj n a hmass

/--
[fkRectCritical_zeroTurnAbove_le_half_of_sourceMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnCutTopology.lean)
-/
@[path]
private lemma fkRectCritical_zeroTurnAbove_le_half_of_sourceMass_eq
  {R : FKRectTorus}
  {q : Real}
  {n : Nat}
  {a : Real}
-- given
  (hq : 1 <= q)
  (hinj : forall omega : R.Configuration, fkRectZeroTurnCutRemainderCount R omega <= fkRectRawPrimalDualHorizontalCrossingClusterCount R (fkRectForceCutClosed R omega))
  (hmass : forall S : Finset (Fin (2 * R.height)), S.card = n + 1 -> fkRectCriticalEventMass R q {eta | FKRectPrimalDualCrossingSourceWitness R S eta} <= a ^ (n + 1))
  (hsmall : Nat.choose (2 * R.height) (n + 1) * a ^ (n + 1) <= FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) / 2) :
-- imply
  fkRectCriticalZeroTurnAboveMass R q (2 * R.width + n) <= (1 : Real) / 2 := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_zeroTurnAbove_le_half_of_sourceMass R hq hinj n a hmass hsmall

/--
[fkRectCritical_zeroTurnAbove_le_half_of_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnCutTopology.lean)
-/
@[path]
private lemma fkRectCritical_zeroTurnAbove_le_half_of_step_eq
  {R : FKRectTorus}
  {q : Real}
  {n : Nat}
  {a : Real}
-- given
  (hq : 1 <= q)
  (hinj : forall omega : R.Configuration, fkRectZeroTurnCutRemainderCount R omega <= fkRectRawPrimalDualHorizontalCrossingClusterCount R (fkRectForceCutClosed R omega))
  (ha : 0 <= a)
  (hstep : forall (T : Finset (Fin (2 * R.height))) (i : Fin (2 * R.height)), i ∉ T -> fkRectCriticalEventMass R q {eta | FKRectPrimalDualCrossingSourceWitness R (insert i T) eta} <= a * fkRectCriticalEventMass R q {eta | FKRectPrimalDualCrossingSourceWitness R T eta})
  (hsmall : Nat.choose (2 * R.height) (n + 1) * a ^ (n + 1) <= FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) / 2) :
-- imply
  fkRectCriticalZeroTurnAboveMass R q (2 * R.width + n) <= (1 : Real) / 2 := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_zeroTurnAbove_le_half_of_step R hq hinj n ha hstep hsmall

/--
[fkRectCritical_zeroTurnAbove_le_half_of_cutFreeStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnCutTopology.lean)
-/
@[path]
private lemma fkRectCritical_zeroTurnAbove_le_half_of_cutFreeStep_eq
  {R : FKRectTorus}
  {q : Real}
  {n : Nat}
  {a : Real}
-- given
  (hq : 1 <= q)
  (hinj : forall omega : R.Configuration, fkRectZeroTurnCutRemainderCount R omega <= fkRectRawPrimalDualHorizontalCrossingClusterCount R (fkRectForceCutClosed R omega))
  (ha : 0 <= a)
  (hstep : forall (T : Finset (Fin (2 * R.height))) (i : Fin (2 * R.height)), i ∉ T -> fkRectCriticalCutFreeEventMass R q {eta | FKRectPrimalDualCrossingSourceWitnessCore R (insert i T) eta} <= a * fkRectCriticalCutFreeEventMass R q {eta | FKRectPrimalDualCrossingSourceWitnessCore R T eta})
  (hsmall : Nat.choose (2 * R.height) (n + 1) * a ^ (n + 1) <= FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) / 2) :
-- imply
  fkRectCriticalZeroTurnAboveMass R q (2 * R.width + n) <= (1 : Real) / 2 := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_zeroTurnAbove_le_half_of_cutFreeStep R hq hinj n ha hstep hsmall

/--
[zeroTurnCost_div_two_q_le_allSectorNormalization_of_sourceMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnCutTopology.lean)
-/
@[path]
private lemma zeroTurnCost_div_two_q_le_allSectorNormalization_of_sourceMass_eq
  {R : FKRectTorus}
  {q : Real}
  {n : Nat}
  {a : Real}
-- given
  (hq : 4 < q)
  (hinj : forall omega : R.Configuration, fkRectZeroTurnCutRemainderCount R omega <= fkRectRawPrimalDualHorizontalCrossingClusterCount R (fkRectForceCutClosed R omega))
  (hmass : forall S : Finset (Fin (2 * R.height)), S.card = n + 1 -> fkRectCriticalEventMass R q {eta | FKRectPrimalDualCrossingSourceWitness R S eta} <= a ^ (n + 1))
  (hsmall : Nat.choose (2 * R.height) (n + 1) * a ^ (n + 1) <= FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) / 2) :
-- imply
  (2 / Real.sqrt q) ^ (2 * R.width + n) / (2 * q) <= fkRectAllSectorNormalization R q := by
-- proof
  apply StatMech.FrontierD.zeroTurnCost_div_two_q_le_allSectorNormalization_of_sourceMass R hq hinj n a hmass hsmall

/--
[zeroTurnCost_div_two_q_le_allSectorNormalization_of_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnCutTopology.lean)
-/
@[path]
private lemma zeroTurnCost_div_two_q_le_allSectorNormalization_of_step_eq
  {R : FKRectTorus}
  {q : Real}
  {n : Nat}
  {a : Real}
-- given
  (hq : 4 < q)
  (hinj : forall omega : R.Configuration, fkRectZeroTurnCutRemainderCount R omega <= fkRectRawPrimalDualHorizontalCrossingClusterCount R (fkRectForceCutClosed R omega))
  (ha : 0 <= a)
  (hstep : forall (T : Finset (Fin (2 * R.height))) (i : Fin (2 * R.height)), i ∉ T -> fkRectCriticalEventMass R q {eta | FKRectPrimalDualCrossingSourceWitness R (insert i T) eta} <= a * fkRectCriticalEventMass R q {eta | FKRectPrimalDualCrossingSourceWitness R T eta})
  (hsmall : Nat.choose (2 * R.height) (n + 1) * a ^ (n + 1) <= FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) / 2) :
-- imply
  (2 / Real.sqrt q) ^ (2 * R.width + n) / (2 * q) <= fkRectAllSectorNormalization R q := by
-- proof
  apply StatMech.FrontierD.zeroTurnCost_div_two_q_le_allSectorNormalization_of_step R hq hinj n ha hstep hsmall

/--
[zeroTurnCost_div_two_q_le_allSectorNormalization_of_cutFreeStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnCutTopology.lean)
-/
@[path]
private lemma zeroTurnCost_div_two_q_le_allSectorNormalization_of_cutFreeStep_eq
  {R : FKRectTorus}
  {q : Real}
  {n : Nat}
  {a : Real}
-- given
  (hq : 4 < q)
  (hinj : forall omega : R.Configuration, fkRectZeroTurnCutRemainderCount R omega <= fkRectRawPrimalDualHorizontalCrossingClusterCount R (fkRectForceCutClosed R omega))
  (ha : 0 <= a)
  (hstep : forall (T : Finset (Fin (2 * R.height))) (i : Fin (2 * R.height)), i ∉ T -> fkRectCriticalCutFreeEventMass R q {eta | FKRectPrimalDualCrossingSourceWitnessCore R (insert i T) eta} <= a * fkRectCriticalCutFreeEventMass R q {eta | FKRectPrimalDualCrossingSourceWitnessCore R T eta})
  (hsmall : Nat.choose (2 * R.height) (n + 1) * a ^ (n + 1) <= FK.cFE (fkRectCriticalP q) q ^ (2 * R.width + R.height) / 2) :
-- imply
  (2 / Real.sqrt q) ^ (2 * R.width + n) / (2 * q) <= fkRectAllSectorNormalization R q := by
-- proof
  apply StatMech.FrontierD.zeroTurnCost_div_two_q_le_allSectorNormalization_of_cutFreeStep R hq hinj n ha hstep hsmall


-- created on 2026-10-23
