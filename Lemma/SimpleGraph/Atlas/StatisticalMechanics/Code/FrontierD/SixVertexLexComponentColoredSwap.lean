import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLexComponentColoredSwap.Part3
open Finset StatMech StatMech.FrontierD


/--
[sixVertexTorusEdgeMaskVertexMask_eq_true_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLexComponentColoredSwap.lean)
-/
@[path]
private lemma sixVertexTorusEdgeMaskVertexMask_eq_true_iff_eq
  {T : EvenTorus}
  {edgeMask : SixVertexArrows T}
  {v : T.Vertex} :
-- imply
  sixVertexTorusEdgeMaskVertexMask edgeMask v = true ↔ ∃ side : Fin 4, sixVertexTorusLocalSwitchMask edgeMask v side = true := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusEdgeMaskVertexMask_eq_true_iff edgeMask v

/--
[sixVertexTorusLocalSwitchMask_bondMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLexComponentColoredSwap.lean)
-/
@[path]
private lemma sixVertexTorusLocalSwitchMask_bondMate_eq
  {T : EvenTorus}
  {edgeMask : SixVertexArrows T}
  {d : SixVertexTorusDart T} :
-- imply
  sixVertexTorusLocalSwitchMask edgeMask (sixVertexTorusDartBondMate T d).1 (sixVertexTorusDartBondMate T d).2 = sixVertexTorusLocalSwitchMask edgeMask d.1 d.2 := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusLocalSwitchMask_bondMate edgeMask d

/--
[sixVertexLexDisagreementComponentVertexMask_bondMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLexComponentColoredSwap.lean)
-/
@[path]
private lemma sixVertexLexDisagreementComponentVertexMask_bondMate_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {d : SixVertexTorusDart T}
-- given
  (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty)
  (hdisagrees : sixVertexTorusEdgeDisagrees omega eta (sixVertexTorusDartEdge T d)) :
-- imply
  sixVertexLexDisagreementComponentVertexMask T omega eta h d.1 = sixVertexLexDisagreementComponentVertexMask T omega eta h (sixVertexTorusDartBondMate T d).1 := by
-- proof
  apply StatMech.FrontierD.sixVertexLexDisagreementComponentVertexMask_bondMate T omega eta h d hdisagrees

/--
[sixVertexLexDisagreementComponentVertexMask_eq_localMask_of_disagrees](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLexComponentColoredSwap.lean)
-/
@[path]
private lemma sixVertexLexDisagreementComponentVertexMask_eq_localMask_of_disagrees_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {d : SixVertexTorusDart T}
-- given
  (h : (sixVertexPositiveSeamDisagreements T omega eta).Nonempty)
  (hdisagrees : sixVertexTorusEdgeDisagrees omega eta (sixVertexTorusDartEdge T d)) :
-- imply
  sixVertexLexDisagreementComponentVertexMask T omega eta h d.1 = sixVertexTorusLocalSwitchMask (sixVertexLexDisagreementComponentMask T omega eta h) d.1 d.2 := by
-- proof
  apply StatMech.FrontierD.sixVertexLexDisagreementComponentVertexMask_eq_localMask_of_disagrees T omega eta h d hdisagrees

/--
[sixVertexLexDisagreementComponent_fullSwapBondCoherent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLexComponentColoredSwap.lean)
-/
@[path]
private lemma sixVertexLexDisagreementComponent_fullSwapBondCoherent_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
-- given
  (h : (sixVertexPositiveSeamDisagreements T (source false).arrows (source true).arrows).Nonempty) :
-- imply
  FKColoredFullSwapBondCoherent source (sixVertexLexDisagreementComponentVertexMask T (source false).arrows (source true).arrows h) := by
-- proof
  apply StatMech.FrontierD.sixVertexLexDisagreementComponent_fullSwapBondCoherent source h

/--
[sixVertexLexDisagreementComponentColoredTarget_false_arrows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLexComponentColoredSwap.lean)
-/
@[path]
private lemma sixVertexLexDisagreementComponentColoredTarget_false_arrows_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
-- given
  (h : (sixVertexPositiveSeamDisagreements T (source false).arrows (source true).arrows).Nonempty) :
-- imply
  (sixVertexLexDisagreementComponentColoredTarget source h false).arrows = sixVertexTorusSwitchFirst (sixVertexLexDisagreementComponentMask T (source false).arrows (source true).arrows h) (source false).arrows (source true).arrows := by
-- proof
  apply StatMech.FrontierD.sixVertexLexDisagreementComponentColoredTarget_false_arrows source h

/--
[sixVertexLexDisagreementComponentColoredTarget_true_arrows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLexComponentColoredSwap.lean)
-/
@[path]
private lemma sixVertexLexDisagreementComponentColoredTarget_true_arrows_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
-- given
  (h : (sixVertexPositiveSeamDisagreements T (source false).arrows (source true).arrows).Nonempty) :
-- imply
  (sixVertexLexDisagreementComponentColoredTarget source h true).arrows = sixVertexTorusSwitchSecond (sixVertexLexDisagreementComponentMask T (source false).arrows (source true).arrows h) (source false).arrows (source true).arrows := by
-- proof
  apply StatMech.FrontierD.sixVertexLexDisagreementComponentColoredTarget_true_arrows source h

/--
[sixVertexLexDisagreementComponentColoredTarget_middle_of_transfer_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLexComponentColoredSwap.lean)
-/
@[path]
private lemma sixVertexLexDisagreementComponentColoredTarget_middle_of_transfer_one_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {middle : Nat}
-- given
  (hlower : sixVertexUpCount (svTorusVerticalRows T (source false).arrows (svFinLast T.height_pos)) = middle - 1)
  (hupper : sixVertexUpCount (svTorusVerticalRows T (source true).arrows (svFinLast T.height_pos)) = middle + 1)
  (hmiddle : 0 < middle)
  (h : (sixVertexPositiveSeamDisagreements T (source false).arrows (source true).arrows).Nonempty)
  (htransfer : sixVertexTorusMaskSeamTransfer (sixVertexLexDisagreementComponentMask T (source false).arrows (source true).arrows h) (source false).arrows (source true).arrows = 1) :
-- imply
  let target := sixVertexLexDisagreementComponentColoredTarget source h sixVertexUpCount (svTorusVerticalRows T (target false).arrows (svFinLast T.height_pos)) = middle /\ sixVertexUpCount (svTorusVerticalRows T (target true).arrows (svFinLast T.height_pos)) = middle /\ sixVertexHorizontalPairBoundedFineRowProfile ((target false).arrows.horizontal, (target true).arrows.horizontal) = sixVertexHorizontalPairBoundedFineRowProfile ((source false).arrows.horizontal, (source true).arrows.horizontal) := by
-- proof
  apply StatMech.FrontierD.sixVertexLexDisagreementComponentColoredTarget_middle_of_transfer_one source middle hlower hupper hmiddle h htransfer


-- created on 2026-10-23
