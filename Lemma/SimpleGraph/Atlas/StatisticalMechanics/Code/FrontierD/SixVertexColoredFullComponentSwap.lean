import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredFullComponentSwap.Part3
open StatMech StatMech.FrontierD


/--
[sixVertexTorusDartOfMedialDart_bondMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredFullComponentSwap.lean)
-/
@[path]
private lemma sixVertexTorusDartOfMedialDart_bondMate_eq
  {T : EvenTorus}
  {d : FKMedialDart T} :
-- imply
  sixVertexTorusDartOfMedialDart (fkMedialBondMate T d) = sixVertexTorusDartBondMate T (sixVertexTorusDartOfMedialDart d) := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusDartOfMedialDart_bondMate T d

/--
[fkColoredPair_crossLayerColor_eq_iff_edgeArrow_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredFullComponentSwap.lean)
-/
@[path]
private lemma fkColoredPair_crossLayerColor_eq_iff_edgeArrow_eq_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {d : FKMedialDart T} :
-- imply
  (source false).color d = (source true).color d ↔ sixVertexTorusEdgeArrow (source false).arrows (sixVertexTorusDartEdge T (sixVertexTorusDartOfMedialDart d)) = sixVertexTorusEdgeArrow (source true).arrows (sixVertexTorusDartEdge T (sixVertexTorusDartOfMedialDart d)) := by
-- proof
  apply StatMech.FrontierD.fkColoredPair_crossLayerColor_eq_iff_edgeArrow_eq source d

/--
[fkColoredFullSwapTarget_pairing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredFullComponentSwap.lean)
-/
@[path]
private lemma fkColoredFullSwapTarget_pairing_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {layer : Bool}
  {v : T.Vertex}
-- given
  (mask : T.Vertex -> Bool)
  (hbond : FKColoredFullSwapBondCoherent source mask) :
-- imply
  (fkColoredFullSwapTarget source mask hbond layer).pairing v = if mask v then (source (!layer)).pairing v else (source layer).pairing v := by
-- proof
  apply StatMech.FrontierD.fkColoredFullSwapTarget_pairing source mask hbond layer v

/--
[fkColoredFullSwapTarget_color](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredFullComponentSwap.lean)
-/
@[path]
private lemma fkColoredFullSwapTarget_color_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {layer : Bool}
  {d : FKMedialDart T}
-- given
  (mask : T.Vertex -> Bool)
  (hbond : FKColoredFullSwapBondCoherent source mask) :
-- imply
  (fkColoredFullSwapTarget source mask hbond layer).color d = if mask d.1 then (source (!layer)).color d else (source layer).color d := by
-- proof
  apply StatMech.FrontierD.fkColoredFullSwapTarget_color source mask hbond layer d

/--
[fkColoredFullSwapTarget_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredFullComponentSwap.lean)
-/
@[path]
private lemma fkColoredFullSwapTarget_horizontal_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {layer : Bool}
  {v : T.Vertex}
-- given
  (mask : T.Vertex -> Bool)
  (hbond : FKColoredFullSwapBondCoherent source mask) :
-- imply
  (fkColoredFullSwapTarget source mask hbond layer).arrows.horizontal v = if mask v then (source (!layer)).arrows.horizontal v else (source layer).arrows.horizontal v := by
-- proof
  apply StatMech.FrontierD.fkColoredFullSwapTarget_horizontal source mask hbond layer v

/--
[fkColoredFullSwapTarget_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredFullComponentSwap.lean)
-/
@[path]
private lemma fkColoredFullSwapTarget_vertical_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {layer : Bool}
  {v : T.Vertex}
-- given
  (mask : T.Vertex -> Bool)
  (hbond : FKColoredFullSwapBondCoherent source mask) :
-- imply
  (fkColoredFullSwapTarget source mask hbond layer).arrows.vertical v = if mask v then (source (!layer)).arrows.vertical v else (source layer).arrows.vertical v := by
-- proof
  apply StatMech.FrontierD.fkColoredFullSwapTarget_vertical source mask hbond layer v

/--
[fkColoredFullSwapTarget_bondCoherent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredFullComponentSwap.lean)
-/
@[path]
private lemma fkColoredFullSwapTarget_bondCoherent_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
-- given
  (mask : T.Vertex -> Bool)
  (hbond : FKColoredFullSwapBondCoherent source mask) :
-- imply
  FKColoredFullSwapBondCoherent (fkColoredFullSwapTarget source mask hbond) mask := by
-- proof
  apply StatMech.FrontierD.fkColoredFullSwapTarget_bondCoherent source mask hbond

/--
[fkColoredFullSwapTarget_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredFullComponentSwap.lean)
-/
@[path]
private lemma fkColoredFullSwapTarget_involutive_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
-- given
  (mask : T.Vertex -> Bool)
  (hbond : FKColoredFullSwapBondCoherent source mask) :
-- imply
  fkColoredFullSwapTarget (fkColoredFullSwapTarget source mask hbond) mask (fkColoredFullSwapTarget_bondCoherent source mask hbond) = source := by
-- proof
  apply StatMech.FrontierD.fkColoredFullSwapTarget_involutive source mask hbond

/--
[fkColoredFullSwapTarget_slotColor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredFullComponentSwap.lean)
-/
@[path]
private lemma fkColoredFullSwapTarget_slotColor_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {slot : FKLayeredStrandSlot T}
-- given
  (mask : T.Vertex -> Bool)
  (hbond : FKColoredFullSwapBondCoherent source mask) :
-- imply
  fkColoredLayeredSlotColor (fkColoredFullSwapTarget source mask hbond) slot = fkColoredLayeredSlotColor source (fkColoredFullSwapLayeredSlotEquiv mask slot) := by
-- proof
  apply StatMech.FrontierD.fkColoredFullSwapTarget_slotColor source mask hbond slot

/--
[fkColoredFullSwapTarget_trueStrandSlotCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredFullComponentSwap.lean)
-/
@[path]
private lemma fkColoredFullSwapTarget_trueStrandSlotCount_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
-- given
  (mask : T.Vertex -> Bool)
  (hbond : FKColoredFullSwapBondCoherent source mask) :
-- imply
  fkColoredTrueStrandSlotCount (fkColoredFullSwapTarget source mask hbond) = fkColoredTrueStrandSlotCount source := by
-- proof
  apply StatMech.FrontierD.fkColoredFullSwapTarget_trueStrandSlotCount source mask hbond

/--
[fkColoredFullSwapTarget_totalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredFullComponentSwap.lean)
-/
@[path]
private lemma fkColoredFullSwapTarget_totalC_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
-- given
  (mask : T.Vertex -> Bool)
  (hbond : FKColoredFullSwapBondCoherent source mask) :
-- imply
  fkColoredLoopPairingPairTotalC (fkColoredFullSwapTarget source mask hbond) = fkColoredLoopPairingPairTotalC source := by
-- proof
  apply StatMech.FrontierD.fkColoredFullSwapTarget_totalC source mask hbond

/--
[fkColoredFullSwapTarget_bigrade](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredFullComponentSwap.lean)
-/
@[path]
private lemma fkColoredFullSwapTarget_bigrade_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
-- given
  (mask : T.Vertex -> Bool)
  (hbond : FKColoredFullSwapBondCoherent source mask) :
-- imply
  (fkColoredLoopPairingPairTotalC (fkColoredFullSwapTarget source mask hbond), fkColoredTrueStrandSlotCount (fkColoredFullSwapTarget source mask hbond)) = (fkColoredLoopPairingPairTotalC source, fkColoredTrueStrandSlotCount source) := by
-- proof
  apply StatMech.FrontierD.fkColoredFullSwapTarget_bigrade source mask hbond


-- created on 2026-10-23
