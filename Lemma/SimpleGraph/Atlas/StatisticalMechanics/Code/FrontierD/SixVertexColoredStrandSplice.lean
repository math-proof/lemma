import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice.Part11
open Finset StatMech StatMech.FrontierD


/--
[fkColoredSideSlot_west](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean)
-/
@[path]
private lemma fkColoredSideSlot_west_eq
  {pairing : Bool} :
-- imply
  fkColoredSideSlot pairing .west = false := by
-- proof
  apply StatMech.FrontierD.fkColoredSideSlot_west pairing

/--
[fkColoredSideSlot_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean)
-/
@[path]
private lemma fkColoredSideSlot_east_eq
  {pairing : Bool} :
-- imply
  fkColoredSideSlot pairing .east = true := by
-- proof
  apply StatMech.FrontierD.fkColoredSideSlot_east pairing

/--
[fkColoredSideSlot_localMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean)
-/
@[path]
private lemma fkColoredSideSlot_localMate_eq
  {pairing : Bool}
  {side : FKMedialSide} :
-- imply
  fkColoredSideSlot pairing (fkMedialLocalSideMate pairing side) = fkColoredSideSlot pairing side := by
-- proof
  apply StatMech.FrontierD.fkColoredSideSlot_localMate pairing side

/--
[FKColoredLoopPairing.color_eq_slotColor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean)
-/
@[path]
private lemma color_eq_slotColor_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {layer : Bool}
  {v : T.Vertex}
  {side : FKMedialSide} :
-- imply
  (source layer).color (v, side) = fkColoredLayeredSlotColor source (layer, v, fkColoredSideSlot ((source layer).pairing v) side) := by
-- proof
  apply StatMech.FrontierD.FKColoredLoopPairing.color_eq_slotColor source layer v side

/--
[fkColoredStrandSpliceRawColor_localMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean)
-/
@[path]
private lemma fkColoredStrandSpliceRawColor_localMate_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {slotEquiv : FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T}
  {layer : Bool}
  {d : FKMedialDart T}
-- given
  (targetPairing : Bool -> FKMedialLoopPairing T) :
-- imply
  fkColoredStrandSpliceRawColor source targetPairing slotEquiv (layer, fkMedialLocalMate (targetPairing layer) d) = fkColoredStrandSpliceRawColor source targetPairing slotEquiv (layer, d) := by
-- proof
  apply StatMech.FrontierD.fkColoredStrandSpliceRawColor_localMate source targetPairing slotEquiv layer d

/--
[fkColoredStrandSpliceBondCoherent_iff_boundaryInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean)
-/
@[path]
private lemma fkColoredStrandSpliceBondCoherent_iff_boundaryInvariant_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {slotEquiv : FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T}
-- given
  (targetPairing : Bool -> FKMedialLoopPairing T) :
-- imply
  FKColoredStrandSpliceBondCoherent source targetPairing slotEquiv ↔ forall x : FKLayeredMedialDart T, fkColoredStrandSpliceRawColor source targetPairing slotEquiv (x.1, fkMedialBoundaryStep (targetPairing x.1) x.2) = fkColoredStrandSpliceRawColor source targetPairing slotEquiv x := by
-- proof
  apply StatMech.FrontierD.fkColoredStrandSpliceBondCoherent_iff_boundaryInvariant source targetPairing slotEquiv

/--
[card_boolFalseFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean)
-/
@[path]
private lemma card_boolFalseFiber_eq
  [Fintype A]
-- given
  (color : A -> Bool) :
-- imply
  Fintype.card {x : A // color x = false} = Fintype.card A - Fintype.card {x : A // color x = true} := by
-- proof
  apply StatMech.FrontierD.card_boolFalseFiber color

/--
[fkColoredStrandSlotEquivOfFiberCards_color](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean)
-/
@[path]
private lemma fkColoredStrandSlotEquivOfFiberCards_color_eq
  {T : EvenTorus}
  {source target : FKColoredLoopPairingPair T}
-- given
  (hcard : forall color : Bool, Fintype.card {slot : FKLayeredStrandSlot T // fkColoredLayeredSlotColor target slot = color} = Fintype.card {slot : FKLayeredStrandSlot T // fkColoredLayeredSlotColor source slot = color}) :
-- imply
  FKColoredStrandSlotColorEquiv source target (fkColoredStrandSlotEquivOfFiberCards source target hcard) := by
-- proof
  apply StatMech.FrontierD.fkColoredStrandSlotEquivOfFiberCards_color source target hcard

/--
[fkColoredStrandSlotFiberCards_of_trueCount_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean)
-/
@[path]
private lemma fkColoredStrandSlotFiberCards_of_trueCount_eq_eq
  {T : EvenTorus}
  {source target : FKColoredLoopPairingPair T}
-- given
  (htrue : fkColoredTrueStrandSlotCount source = fkColoredTrueStrandSlotCount target) :
-- imply
  forall color : Bool, Fintype.card {slot : FKLayeredStrandSlot T // fkColoredLayeredSlotColor target slot = color} = Fintype.card {slot : FKLayeredStrandSlot T // fkColoredLayeredSlotColor source slot = color} := by
-- proof
  apply StatMech.FrontierD.fkColoredStrandSlotFiberCards_of_trueCount_eq source target htrue

/--
[fkColoredStrandSlotEquivOfTrueCount_color](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean)
-/
@[path]
private lemma fkColoredStrandSlotEquivOfTrueCount_color_eq
  {T : EvenTorus}
  {source target : FKColoredLoopPairingPair T}
-- given
  (htrue : fkColoredTrueStrandSlotCount source = fkColoredTrueStrandSlotCount target) :
-- imply
  FKColoredStrandSlotColorEquiv source target (fkColoredStrandSlotEquivOfTrueCount source target htrue) := by
-- proof
  apply StatMech.FrontierD.fkColoredStrandSlotEquivOfTrueCount_color source target htrue

/--
[fkColoredStrandSpliceRawColor_eq_of_colorEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean)
-/
@[path]
private lemma fkColoredStrandSpliceRawColor_eq_of_colorEquiv_eq
  {T : EvenTorus}
  {source target : FKColoredLoopPairingPair T}
  {slotEquiv : FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T}
  {x : FKLayeredMedialDart T}
-- given
  (hcolor : FKColoredStrandSlotColorEquiv source target slotEquiv) :
-- imply
  fkColoredStrandSpliceRawColor source (fun layer => (target layer).pairing) slotEquiv x = (target x.1).color x.2 := by
-- proof
  apply StatMech.FrontierD.fkColoredStrandSpliceRawColor_eq_of_colorEquiv source target slotEquiv hcolor x

/--
[FKColoredStrandSplice.ofColorEquiv_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean)
-/
@[path]
private lemma ofColorEquiv_target_eq
  {T : EvenTorus}
  {source target : FKColoredLoopPairingPair T}
  {slotEquiv : FKLayeredStrandSlot T ≃ FKLayeredStrandSlot T}
-- given
  (hcolor : FKColoredStrandSlotColorEquiv source target slotEquiv) :
-- imply
  (FKColoredStrandSplice.ofColorEquiv source target slotEquiv hcolor).target = target := by
-- proof
  apply StatMech.FrontierD.FKColoredStrandSplice.ofColorEquiv_target source target slotEquiv hcolor

/--
[FKColoredStrandSplice.target_slotColor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean)
-/
@[path]
private lemma target_slotColor_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {splice : FKColoredStrandSplice source}
  {slot : FKLayeredStrandSlot T} :
-- imply
  fkColoredLayeredSlotColor splice.target slot = fkColoredLayeredSlotColor source (splice.slotEquiv slot) := by
-- proof
  apply StatMech.FrontierD.FKColoredStrandSplice.target_slotColor splice slot

/--
[FKColoredStrandSplice.target_trueStrandSlotCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean)
-/
@[path]
private lemma target_trueStrandSlotCount_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {splice : FKColoredStrandSplice source} :
-- imply
  fkColoredTrueStrandSlotCount splice.target = fkColoredTrueStrandSlotCount source := by
-- proof
  apply StatMech.FrontierD.FKColoredStrandSplice.target_trueStrandSlotCount splice

/--
[FKColoredStrandSplice.symm_rawColor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean)
-/
@[path]
private lemma symm_rawColor_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {splice : FKColoredStrandSplice source}
  {x : FKLayeredMedialDart T} :
-- imply
  fkColoredStrandSpliceRawColor splice.target (fun layer => (source layer).pairing) splice.slotEquiv.symm x = (source x.1).color x.2 := by
-- proof
  apply StatMech.FrontierD.FKColoredStrandSplice.symm_rawColor splice x

/--
[FKColoredStrandSplice.symm_bondCoherent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean)
-/
@[path]
private lemma symm_bondCoherent_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {splice : FKColoredStrandSplice source} :
-- imply
  FKColoredStrandSpliceBondCoherent splice.target (fun layer => (source layer).pairing) splice.slotEquiv.symm := by
-- proof
  apply StatMech.FrontierD.FKColoredStrandSplice.symm_bondCoherent splice

/--
[FKColoredStrandSplice.symm_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean)
-/
@[path]
private lemma symm_target_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {splice : FKColoredStrandSplice source} :
-- imply
  splice.symm.target = source := by
-- proof
  apply StatMech.FrontierD.FKColoredStrandSplice.symm_target splice

/--
[fkColoredLoopPairingPairTotalC_eq_slotPairEqualCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean)
-/
@[path]
private lemma fkColoredLoopPairingPairTotalC_eq_slotPairEqualCount_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T} :
-- imply
  fkColoredLoopPairingPairTotalC source = fkColoredSlotPairEqualCount source (Equiv.refl _) := by
-- proof
  apply StatMech.FrontierD.fkColoredLoopPairingPairTotalC_eq_slotPairEqualCount source

/--
[FKColoredStrandSplice.target_totalC_eq_slotPairEqualCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean)
-/
@[path]
private lemma target_totalC_eq_slotPairEqualCount_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {splice : FKColoredStrandSplice source} :
-- imply
  fkColoredLoopPairingPairTotalC splice.target = fkColoredSlotPairEqualCount source splice.slotEquiv := by
-- proof
  apply StatMech.FrontierD.FKColoredStrandSplice.target_totalC_eq_slotPairEqualCount splice

/--
[FKColoredStrandSplice.target_totalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean)
-/
@[path]
private lemma target_totalC_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {splice : FKColoredStrandSplice source}
-- given
  (hC : splice.PreservesTotalC) :
-- imply
  fkColoredLoopPairingPairTotalC splice.target = fkColoredLoopPairingPairTotalC source := by
-- proof
  apply StatMech.FrontierD.FKColoredStrandSplice.target_totalC splice hC

/--
[FKColoredStrandSplice.target_upCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean)
-/
@[path]
private lemma target_upCount_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {splice : FKColoredStrandSplice source}
  {layer : Bool} :
-- imply
  (sixVertexUpCount (svTorusVerticalRows T (splice.target layer).arrows (svFinLast T.height_pos)) : Int) = (sixVertexUpCount (svTorusVerticalRows T (source layer).arrows (svFinLast T.height_pos)) : Int) + splice.seamDelta layer := by
-- proof
  apply StatMech.FrontierD.FKColoredStrandSplice.target_upCount splice layer

/--
[FKColoredStrandSplice.target_middleSectors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean)
-/
@[path]
private lemma target_middleSectors_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {splice : FKColoredStrandSplice source}
  {n : Nat}
-- given
  (hn : 0 < n)
  (hlower : sixVertexUpCount (svTorusVerticalRows T (source false).arrows (svFinLast T.height_pos)) = n - 1)
  (hupper : sixVertexUpCount (svTorusVerticalRows T (source true).arrows (svFinLast T.height_pos)) = n + 1)
  (hdeltaLower : splice.seamDelta false = 1)
  (hdeltaUpper : splice.seamDelta true = -1) :
-- imply
  sixVertexUpCount (svTorusVerticalRows T (splice.target false).arrows (svFinLast T.height_pos)) = n /\ sixVertexUpCount (svTorusVerticalRows T (splice.target true).arrows (svFinLast T.height_pos)) = n := by
-- proof
  apply StatMech.FrontierD.FKColoredStrandSplice.target_middleSectors splice n hn hlower hupper hdeltaLower hdeltaUpper


-- created on 2026-10-23
