import Mathlib
import sympy.Basic
import Def.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairLoopFiber.Part5
open Finset Matrix Polynomial StatMech StatMech.FrontierD


/--
[card_localCompatibleLoopPairing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairLoopFiber.lean)
-/
@[path]
private lemma card_localCompatibleLoopPairing_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
  {v : T.Vertex}
-- given
  (homega : omega.IceRule) :
-- imply
  Fintype.card {pairing : Bool // fkLoopPairingCompatible pairing omega v} = if omega.IsCType v then 2 else 1 := by
-- proof
  apply StatMech.FrontierD.card_localCompatibleLoopPairing omega homega v

/--
[card_sixVertexCompatibleLoopPairing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairLoopFiber.lean)
-/
@[path]
private lemma card_sixVertexCompatibleLoopPairing_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
-- given
  (homega : omega.IceRule) :
-- imply
  Fintype.card (SixVertexCompatibleLoopPairing omega) = 2 ^ sixVertexTorusCTypeCount omega := by
-- proof
  apply StatMech.FrontierD.card_sixVertexCompatibleLoopPairing omega homega

/--
[sixVertexMarkedDecoratedPairZeroEquivLoop_totalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairLoopFiber.lean)
-/
@[path]
private lemma sixVertexMarkedDecoratedPairZeroEquivLoop_totalC_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {decorated : SixVertexMarkedDecoratedPair T left right 0} :
-- imply
  sixVertexLoopDecoratedPairTotalC (sixVertexMarkedDecoratedPairZeroEquivLoop T left right decorated) = sixVertexMarkedDecoratedPairTotalC decorated := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedDecoratedPairZeroEquivLoop_totalC T left right decorated

/--
[exists_injective_decoratedZero_of_loopReconnection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairLoopFiber.lean)
-/
@[path]
private lemma exists_injective_decoratedZero_of_loopReconnection_eq
  {T : EvenTorus}
  {lower middle upper : Fin (T.width + 1)}
-- given
  (hreconnect : SixVertexLoopDecoratedPairTotalCReconnection T lower middle upper) :
-- imply
  exists matching : SixVertexMarkedDecoratedPair T lower upper 0 -> SixVertexMarkedDecoratedPair T middle middle 0, Function.Injective matching /\ forall source, sixVertexMarkedDecoratedPairTotalC source = sixVertexMarkedDecoratedPairTotalC (matching source) := by
-- proof
  apply StatMech.FrontierD.exists_injective_decoratedZero_of_loopReconnection hreconnect

/--
[configurationPairTotalCFiberDominates_of_loopReconnection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairLoopFiber.lean)
-/
@[path]
private lemma configurationPairTotalCFiberDominates_of_loopReconnection_eq
  {T : EvenTorus}
  {lower middle upper : Fin (T.width + 1)}
-- given
  (hreconnect : SixVertexLoopDecoratedPairTotalCReconnection T lower middle upper) :
-- imply
  SixVertexConfigurationPairTotalCFiberDominates T lower middle upper := by
-- proof
  apply StatMech.FrontierD.configurationPairTotalCFiberDominates_of_loopReconnection hreconnect

/--
[configurationPairTotalCReconnection_of_loopReconnection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairLoopFiber.lean)
-/
@[path]
private lemma configurationPairTotalCReconnection_of_loopReconnection_eq
  {T : EvenTorus}
  {lower middle upper : Fin (T.width + 1)}
-- given
  (hreconnect : SixVertexLoopDecoratedPairTotalCReconnection T lower middle upper) :
-- imply
  SixVertexConfigurationPairTotalCReconnection T lower middle upper := by
-- proof
  apply StatMech.FrontierD.configurationPairTotalCReconnection_of_loopReconnection hreconnect


-- created on 2026-10-23
