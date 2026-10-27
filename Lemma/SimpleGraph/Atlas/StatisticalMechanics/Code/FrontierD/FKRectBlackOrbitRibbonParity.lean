import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonParity.Part2
open StatMech StatMech.FrontierD


/--
[fkRectBlackOrbitMedialRibbonFlatSite_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonParity.lean)
-/
@[path]
private lemma fkRectBlackOrbitMedialRibbonFlatSite_injective_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  Function.Injective (fkRectBlackOrbitMedialRibbonFlatSite R omega d) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitMedialRibbonFlatSite_injective R omega d

/--
[fkRectMedialRibbonBlockOffset_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonParity.lean)
-/
@[path]
private lemma fkRectMedialRibbonBlockOffset_zero_eq
  {pairing : Bool}
  {side : FKMedialSide} :
-- imply
  fkRectMedialRibbonBlockOffset pairing side 0 = fkRectMedialRibbonPortOffset side := by
-- proof
  apply StatMech.FrontierD.fkRectMedialRibbonBlockOffset_zero pairing side

/--
[fkRectRibbon_scaled_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonParity.lean)
-/
@[path]
private lemma fkRectRibbon_scaled_succ_eq
  {M : ℕ}
  {i : Fin M}
-- given
  (hM : 0 < M) :
-- imply
  ((((8 * (finitePeriodicSucc hM i).val : Nat) : Int)) : ZMod (8 * M)) = (((8 * i.val : Nat) : Int) + 8 : ZMod (8 * M)) := by
-- proof
  apply StatMech.FrontierD.fkRectRibbon_scaled_succ hM i

/--
[fkRectRibbon_scaled_pred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonParity.lean)
-/
@[path]
private lemma fkRectRibbon_scaled_pred_eq
  {M : ℕ}
  {i : Fin M}
-- given
  (hM : 0 < M) :
-- imply
  ((((8 * (SixVertexArrows.cyclicPred hM i).val : Nat) : Int)) : ZMod (8 * M)) = (((8 * i.val : Nat) : Int) - 8 : ZMod (8 * M)) := by
-- proof
  apply StatMech.FrontierD.fkRectRibbon_scaled_pred hM i

/--
[fkRectRibbon_scaled_succ_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonParity.lean)
-/
@[path]
private lemma fkRectRibbon_scaled_succ_mul_eq
  {M : ℕ}
  {i : Fin M}
-- given
  (hM : 0 < M) :
-- imply
  ((8 : ZMod (8 * M)) * (finitePeriodicSucc hM i).val) = 8 * (i.val : ZMod (8 * M)) + 8 := by
-- proof
  apply StatMech.FrontierD.fkRectRibbon_scaled_succ_mul hM i

/--
[fkRectRibbon_scaled_pred_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonParity.lean)
-/
@[path]
private lemma fkRectRibbon_scaled_pred_mul_eq
  {M : ℕ}
  {i : Fin M}
-- given
  (hM : 0 < M) :
-- imply
  ((8 : ZMod (8 * M)) * (SixVertexArrows.cyclicPred hM i).val) = 8 * (i.val : ZMod (8 * M)) - 8 := by
-- proof
  apply StatMech.FrontierD.fkRectRibbon_scaled_pred_mul hM i

/--
[fkRectMedialRibbonBlockSite_slot_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonParity.lean)
-/
@[path]
private lemma fkRectMedialRibbonBlockSite_slot_succ_eq
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {e : FKMedialBlackDart R.medialTorus}
  {t : Fin 8}
-- given
  (ht : t ≠ Fin.last 7) :
-- imply
  fkRectMedialRibbonBlockSite R pairing e (t + 1) = fkRectRibbonRectStep (8 * R.medialTorus.width) (8 * R.medialTorus.height) (fkRectMedialRibbonBlockDirection (pairing e.1.1) e.1.2 t) (fkRectMedialRibbonBlockSite R pairing e t) := by
-- proof
  apply StatMech.FrontierD.fkRectMedialRibbonBlockSite_slot_succ R pairing e t ht

/--
[fkRectMedialRibbonBlockSite_wrap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonParity.lean)
-/
@[path]
private lemma fkRectMedialRibbonBlockSite_wrap_eq
  {R : FKRectTorus}
  {pairing : FKMedialLoopPairing R.medialTorus}
  {e : FKMedialBlackDart R.medialTorus} :
-- imply
  fkRectMedialRibbonBlockSite R pairing (fkMedialBlackBoundaryPerm pairing e) 0 = fkRectRibbonRectStep (8 * R.medialTorus.width) (8 * R.medialTorus.height) (fkRectMedialRibbonBlockDirection (pairing e.1.1) e.1.2 (Fin.last 7)) (fkRectMedialRibbonBlockSite R pairing e (Fin.last 7)) := by
-- proof
  apply StatMech.FrontierD.fkRectMedialRibbonBlockSite_wrap R pairing e

/--
[fkRectBlackOrbitMedialRibbonIndexedSite_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonParity.lean)
-/
@[path]
private lemma fkRectBlackOrbitMedialRibbonIndexedSite_succ_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus}
  {z : Fin (fkRectBlackOrbitList (fkRectConfigurationToMedialPairing R omega) d).length × Fin 8} :
-- imply
  fkRectBlackOrbitMedialRibbonIndexedSite R omega d (fkRectRibbonIndexSucc (fkRectBlackOrbitList_length_pos (fkRectConfigurationToMedialPairing R omega) d) z) = fkRectRibbonRectStep (8 * R.medialTorus.width) (8 * R.medialTorus.height) (fkRectBlackOrbitMedialRibbonIndexedDirection R omega d z) (fkRectBlackOrbitMedialRibbonIndexedSite R omega d z) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitMedialRibbonIndexedSite_succ R omega d z


-- created on 2026-10-23
