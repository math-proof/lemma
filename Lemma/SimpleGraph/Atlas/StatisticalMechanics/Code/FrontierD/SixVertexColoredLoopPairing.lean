import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part16
open StatMech StatMech.FrontierD


/--
[boolXor_eq_of_ne_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma boolXor_eq_of_ne_ne_eq
  {a b c d : Bool}
-- given
  (hab : a ≠ b)
  (hcd : c ≠ d) :
-- imply
  (a ^^ c) = (b ^^ d) := by
-- proof
  apply StatMech.FrontierD.boolXor_eq_of_ne_ne hab hcd

/--
[sixVertexIsCType_iff_horizontalIncoming_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma sixVertexIsCType_iff_horizontalIncoming_eq_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
  {v : T.Vertex} :
-- imply
  omega.IsCType v ↔ fkLoopWestIncoming omega v = fkLoopEastIncoming omega v := by
-- proof
  apply StatMech.FrontierD.sixVertexIsCType_iff_horizontalIncoming_eq omega v

/--
[FKColoredLoopPairing.ext](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma ext_eq
  {T : EvenTorus}
  {a b : FKColoredLoopPairing T}
-- given
  (hpairing : a.pairing = b.pairing)
  (hcolor : a.color = b.color) :
-- imply
  a = b := by
-- proof
  apply StatMech.FrontierD.FKColoredLoopPairing.ext hpairing hcolor

/--
[FKColoredLoopPairing.incoming_bondMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma incoming_bondMate_eq
  {T : EvenTorus}
  {colored : FKColoredLoopPairing T}
  {d : FKMedialDart T} :
-- imply
  (!colored.incoming (fkMedialBondMate T d)) = colored.incoming d := by
-- proof
  apply StatMech.FrontierD.FKColoredLoopPairing.incoming_bondMate colored d

/--
[FKColoredLoopPairing.incoming_localMate_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma incoming_localMate_ne_eq
  {T : EvenTorus}
  {colored : FKColoredLoopPairing T}
  {d : FKMedialDart T} :
-- imply
  colored.incoming (fkMedialLocalMate colored.pairing d) ≠ colored.incoming d := by
-- proof
  apply StatMech.FrontierD.FKColoredLoopPairing.incoming_localMate_ne colored d

/--
[FKColoredLoopPairing.dartIncoming_arrows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma dartIncoming_arrows_eq
  {T : EvenTorus}
  {colored : FKColoredLoopPairing T}
  {d : FKMedialDart T} :
-- imply
  fkMedialDartIncoming colored.arrows d = colored.incoming d := by
-- proof
  apply StatMech.FrontierD.FKColoredLoopPairing.dartIncoming_arrows colored d

/--
[FKColoredLoopPairing.compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma compatible_eq
  {T : EvenTorus}
  {colored : FKColoredLoopPairing T} :
-- imply
  ∀ v, fkLoopPairingCompatible (colored.pairing v) colored.arrows v := by
-- proof
  apply StatMech.FrontierD.FKColoredLoopPairing.compatible colored

/--
[FKColoredLoopPairing.iceRule](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma iceRule_eq
  {T : EvenTorus}
  {colored : FKColoredLoopPairing T} :
-- imply
  colored.arrows.IceRule := by
-- proof
  apply StatMech.FrontierD.FKColoredLoopPairing.iceRule colored

/--
[FKColoredLoopPairing.cType_iff_color_west_eq_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma cType_iff_color_west_eq_east_eq
  {T : EvenTorus}
  {colored : FKColoredLoopPairing T}
  {v : T.Vertex} :
-- imply
  colored.arrows.IsCType v ↔ colored.color (v, .west) = colored.color (v, .east) := by
-- proof
  apply StatMech.FrontierD.FKColoredLoopPairing.cType_iff_color_west_eq_east colored v

/--
[SixVertexCompatibleLoopPairing.toColored_incoming](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma toColored_incoming_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
  {pairing : SixVertexCompatibleLoopPairing omega}
  {d : FKMedialDart T} :
-- imply
  pairing.toColored.incoming d = fkMedialDartIncoming omega d := by
-- proof
  apply StatMech.FrontierD.SixVertexCompatibleLoopPairing.toColored_incoming pairing d

/--
[SixVertexCompatibleLoopPairing.toColored_arrows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma toColored_arrows_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
  {pairing : SixVertexCompatibleLoopPairing omega} :
-- imply
  pairing.toColored.arrows = omega := by
-- proof
  apply StatMech.FrontierD.SixVertexCompatibleLoopPairing.toColored_arrows pairing

/--
[FKColoredLoopPairing.toCompatible_toColored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma toCompatible_toColored_eq
  {T : EvenTorus}
  {colored : FKColoredLoopPairing T} :
-- imply
  colored.toCompatible.toColored = colored := by
-- proof
  apply StatMech.FrontierD.FKColoredLoopPairing.toCompatible_toColored colored

/--
[FKColoredLocalPairing.ext](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma ext_eq_2
  {a b : FKColoredLocalPairing}
-- given
  (hpairing : a.pairing = b.pairing)
  (hwest : a.west = b.west)
  (heast : a.east = b.east) :
-- imply
  a = b := by
-- proof
  apply StatMech.FrontierD.FKColoredLocalPairing.ext hpairing hwest heast

/--
[FKColoredLocalPairing.sideColor_west](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma sideColor_west_eq
  {cfg : FKColoredLocalPairing} :
-- imply
  cfg.sideColor .west = cfg.west := by
-- proof
  apply StatMech.FrontierD.FKColoredLocalPairing.sideColor_west cfg

/--
[FKColoredLocalPairing.sideColor_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma sideColor_east_eq
  {cfg : FKColoredLocalPairing} :
-- imply
  cfg.sideColor .east = cfg.east := by
-- proof
  apply StatMech.FrontierD.FKColoredLocalPairing.sideColor_east cfg

/--
[fkMedialLocalMate_eq_localSideMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma fkMedialLocalMate_eq_localSideMate_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {v : T.Vertex}
  {side : FKMedialSide} :
-- imply
  fkMedialLocalMate pairing (v, side) = (v, fkMedialLocalSideMate (pairing v) side) := by
-- proof
  apply StatMech.FrontierD.fkMedialLocalMate_eq_localSideMate pairing v side

/--
[FKColoredLocalPairing.sideColor_localMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma sideColor_localMate_eq
  {cfg : FKColoredLocalPairing}
  {side : FKMedialSide} :
-- imply
  cfg.sideColor (fkMedialLocalSideMate cfg.pairing side) = cfg.sideColor side := by
-- proof
  apply StatMech.FrontierD.FKColoredLocalPairing.sideColor_localMate cfg side

/--
[FKColoredLoopPairing.localPairing_sideColor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma localPairing_sideColor_eq
  {T : EvenTorus}
  {colored : FKColoredLoopPairing T}
  {v : T.Vertex}
  {side : FKMedialSide} :
-- imply
  (colored.localPairing v).sideColor side = colored.color (v, side) := by
-- proof
  apply StatMech.FrontierD.FKColoredLoopPairing.localPairing_sideColor colored v side

/--
[fkColoredLocalPairCross_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma fkColoredLocalPairCross_involutive_eq
  {pair : FKColoredLocalPairing × FKColoredLocalPairing} :
-- imply
  fkColoredLocalPairCross (fkColoredLocalPairCross pair) = pair := by
-- proof
  apply StatMech.FrontierD.fkColoredLocalPairCross_involutive pair

/--
[fkColoredLocalPairCrossWest_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma fkColoredLocalPairCrossWest_involutive_eq
  {pair : FKColoredLocalPairing × FKColoredLocalPairing} :
-- imply
  fkColoredLocalPairCrossWest (fkColoredLocalPairCrossWest pair) = pair := by
-- proof
  apply StatMech.FrontierD.fkColoredLocalPairCrossWest_involutive pair

/--
[fkColoredLocalPairOddCross_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma fkColoredLocalPairOddCross_involutive_eq
  {pair : FKColoredLocalPairing × FKColoredLocalPairing} :
-- imply
  fkColoredLocalPairOddCross (fkColoredLocalPairOddCross pair) = pair := by
-- proof
  apply StatMech.FrontierD.fkColoredLocalPairOddCross_involutive pair

/--
[fkColoredLocalPairReconnection_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma fkColoredLocalPairReconnection_involutive_eq
  {pair : FKColoredLocalPairing × FKColoredLocalPairing} :
-- imply
  fkColoredLocalPairReconnection (fkColoredLocalPairReconnection pair) = pair := by
-- proof
  apply StatMech.FrontierD.fkColoredLocalPairReconnection_involutive pair

/--
[fkColoredLocalPairOddCross_cTypeCount_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma fkColoredLocalPairOddCross_cTypeCount_of_odd_eq
  {pair : FKColoredLocalPairing × FKColoredLocalPairing}
-- given
  (hodd : pair.1.west ^^ pair.1.east ^^ pair.2.west ^^ pair.2.east = true) :
-- imply
  fkColoredLocalPairCTypeCount (fkColoredLocalPairOddCross pair) = fkColoredLocalPairCTypeCount pair := by
-- proof
  apply StatMech.FrontierD.fkColoredLocalPairOddCross_cTypeCount_of_odd pair hodd

/--
[fkColoredLocalPairReconnection_cTypeCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma fkColoredLocalPairReconnection_cTypeCount_eq
  {pair : FKColoredLocalPairing × FKColoredLocalPairing} :
-- imply
  fkColoredLocalPairCTypeCount (fkColoredLocalPairReconnection pair) = fkColoredLocalPairCTypeCount pair := by
-- proof
  apply StatMech.FrontierD.fkColoredLocalPairReconnection_cTypeCount pair

/--
[FKColoredLoopPairingPair.localCTypeCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma localCTypeCount_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {v : T.Vertex} :
-- imply
  fkColoredLocalPairCTypeCount ((source false).localPairing v, (source true).localPairing v) = (if (source false).arrows.IsCType v then 1 else 0) + (if (source true).arrows.IsCType v then 1 else 0) := by
-- proof
  apply StatMech.FrontierD.FKColoredLoopPairingPair.localCTypeCount source v

/--
[fkColoredLocalPairCrossIf_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma fkColoredLocalPairCrossIf_involutive_eq
  {cross : Bool}
  {pair : FKColoredLocalPairing × FKColoredLocalPairing} :
-- imply
  fkColoredLocalPairCrossIf cross (fkColoredLocalPairCrossIf cross pair) = pair := by
-- proof
  apply StatMech.FrontierD.fkColoredLocalPairCrossIf_involutive cross pair

/--
[fkColoredLocalPairCrossIf_pairing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma fkColoredLocalPairCrossIf_pairing_eq
  {cross layer : Bool}
  {pair : FKColoredLocalPairing × FKColoredLocalPairing} :
-- imply
  (if layer then (fkColoredLocalPairCrossIf cross pair).2.pairing else (fkColoredLocalPairCrossIf cross pair).1.pairing) = (if layer then pair.2.pairing else pair.1.pairing) := by
-- proof
  apply StatMech.FrontierD.fkColoredLocalPairCrossIf_pairing cross layer pair

/--
[fkColoredVertexCrossRawColor_localMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma fkColoredVertexCrossRawColor_localMate_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {layer : Bool}
  {d : FKMedialDart T}
-- given
  (mask : T.Vertex -> Bool) :
-- imply
  fkColoredVertexCrossRawColor source mask (layer, fkMedialLocalMate (source layer).pairing d) = fkColoredVertexCrossRawColor source mask (layer, d) := by
-- proof
  apply StatMech.FrontierD.fkColoredVertexCrossRawColor_localMate source mask layer d

/--
[fkColoredVertexCrossTarget_localPairing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma fkColoredVertexCrossTarget_localPairing_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {v : T.Vertex}
-- given
  (mask : T.Vertex -> Bool)
  (hbond : FKColoredVertexCrossBondCoherent source mask) :
-- imply
  ((fkColoredVertexCrossTarget source mask hbond false).localPairing v, (fkColoredVertexCrossTarget source mask hbond true).localPairing v) = fkColoredLocalPairCrossIf (mask v) ((source false).localPairing v, (source true).localPairing v) := by
-- proof
  apply StatMech.FrontierD.fkColoredVertexCrossTarget_localPairing source mask hbond v

/--
[fkColoredVertexCrossRawColor_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma fkColoredVertexCrossRawColor_target_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {x : FKLayeredMedialDart T}
-- given
  (mask : T.Vertex -> Bool)
  (hbond : FKColoredVertexCrossBondCoherent source mask) :
-- imply
  fkColoredVertexCrossRawColor (fkColoredVertexCrossTarget source mask hbond) mask x = fkLayeredLoopColor source x := by
-- proof
  apply StatMech.FrontierD.fkColoredVertexCrossRawColor_target source mask hbond x

/--
[fkColoredVertexCrossTarget_bondCoherent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma fkColoredVertexCrossTarget_bondCoherent_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
-- given
  (mask : T.Vertex -> Bool)
  (hbond : FKColoredVertexCrossBondCoherent source mask) :
-- imply
  FKColoredVertexCrossBondCoherent (fkColoredVertexCrossTarget source mask hbond) mask := by
-- proof
  apply StatMech.FrontierD.fkColoredVertexCrossTarget_bondCoherent source mask hbond

/--
[fkColoredVertexCrossTarget_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma fkColoredVertexCrossTarget_involutive_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
-- given
  (mask : T.Vertex -> Bool)
  (hbond : FKColoredVertexCrossBondCoherent source mask) :
-- imply
  fkColoredVertexCrossTarget (fkColoredVertexCrossTarget source mask hbond) mask (fkColoredVertexCrossTarget_bondCoherent source mask hbond) = source := by
-- proof
  apply StatMech.FrontierD.fkColoredVertexCrossTarget_involutive source mask hbond

/--
[fkColoredVertexCrossTarget_totalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma fkColoredVertexCrossTarget_totalC_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
-- given
  (mask : T.Vertex -> Bool)
  (hbond : FKColoredVertexCrossBondCoherent source mask) :
-- imply
  fkColoredLoopPairingPairTotalC (fkColoredVertexCrossTarget source mask hbond) = fkColoredLoopPairingPairTotalC source := by
-- proof
  apply StatMech.FrontierD.fkColoredVertexCrossTarget_totalC source mask hbond

/--
[fkColoredVertexCrossTarget_upCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma fkColoredVertexCrossTarget_upCount_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {layer : Bool}
-- given
  (mask : T.Vertex -> Bool)
  (hbond : FKColoredVertexCrossBondCoherent source mask) :
-- imply
  (sixVertexUpCount (svTorusVerticalRows T (fkColoredVertexCrossTarget source mask hbond layer).arrows (svFinLast T.height_pos)) : Int) = (sixVertexUpCount (svTorusVerticalRows T (source layer).arrows (svFinLast T.height_pos)) : Int) + fkColoredVertexCrossSeamDelta source mask hbond layer := by
-- proof
  apply StatMech.FrontierD.fkColoredVertexCrossTarget_upCount source mask hbond layer

/--
[fkColoredVertexCrossTarget_middleSectors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredLoopPairing.lean)
-/
@[path]
private lemma fkColoredVertexCrossTarget_middleSectors_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {n : Nat}
-- given
  (mask : T.Vertex -> Bool)
  (hbond : FKColoredVertexCrossBondCoherent source mask)
  (hn : 0 < n)
  (hlower : sixVertexUpCount (svTorusVerticalRows T (source false).arrows (svFinLast T.height_pos)) = n - 1)
  (hupper : sixVertexUpCount (svTorusVerticalRows T (source true).arrows (svFinLast T.height_pos)) = n + 1)
  (hdeltaLower : fkColoredVertexCrossSeamDelta source mask hbond false = 1)
  (hdeltaUpper : fkColoredVertexCrossSeamDelta source mask hbond true = -1) :
-- imply
  sixVertexUpCount (svTorusVerticalRows T (fkColoredVertexCrossTarget source mask hbond false).arrows (svFinLast T.height_pos)) = n /\ sixVertexUpCount (svTorusVerticalRows T (fkColoredVertexCrossTarget source mask hbond true).arrows (svFinLast T.height_pos)) = n := by
-- proof
  apply StatMech.FrontierD.fkColoredVertexCrossTarget_middleSectors source mask hbond n hn hlower hupper hdeltaLower hdeltaUpper


-- created on 2026-10-23
