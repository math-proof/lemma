import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexLoopPairBigrade
open StatMech StatMech.FrontierD


/--
[sixVertexLoopDecoratedPairColored_false_arrows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopPairBigrade.lean)
-/
@[path]
private lemma sixVertexLoopDecoratedPairColored_false_arrows_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {decorated : SixVertexLoopDecoratedPair T left right} :
-- imply
  (sixVertexLoopDecoratedPairColored decorated false).arrows = decorated.1.1.1 := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopDecoratedPairColored_false_arrows decorated

/--
[sixVertexLoopDecoratedPairColored_true_arrows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopPairBigrade.lean)
-/
@[path]
private lemma sixVertexLoopDecoratedPairColored_true_arrows_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {decorated : SixVertexLoopDecoratedPair T left right} :
-- imply
  (sixVertexLoopDecoratedPairColored decorated true).arrows = decorated.1.2.1 := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopDecoratedPairColored_true_arrows decorated

/--
[sixVertexLoopDecoratedPairColored_totalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopPairBigrade.lean)
-/
@[path]
private lemma sixVertexLoopDecoratedPairColored_totalC_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {decorated : SixVertexLoopDecoratedPair T left right} :
-- imply
  fkColoredLoopPairingPairTotalC (sixVertexLoopDecoratedPairColored decorated) = sixVertexLoopDecoratedPairTotalC decorated := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopDecoratedPairColored_totalC decorated

/--
[sixVertexLoopDecoratedPairColored_slotColor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopPairBigrade.lean)
-/
@[path]
private lemma sixVertexLoopDecoratedPairColored_slotColor_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {decorated : SixVertexLoopDecoratedPair T left right}
  {slot : FKLayeredStrandSlot T} :
-- imply
  fkColoredLayeredSlotColor (sixVertexLoopDecoratedPairColored decorated) slot = sixVertexArrowPairStrandSlotColor decorated.1.1.1 decorated.1.2.1 slot := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopDecoratedPairColored_slotColor decorated slot

/--
[sixVertexLoopDecoratedPairColored_trueSlotCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopPairBigrade.lean)
-/
@[path]
private lemma sixVertexLoopDecoratedPairColored_trueSlotCount_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {decorated : SixVertexLoopDecoratedPair T left right} :
-- imply
  fkColoredTrueStrandSlotCount (sixVertexLoopDecoratedPairColored decorated) = sixVertexArrowPairTrueStrandSlotCount decorated.1.1.1 decorated.1.2.1 := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopDecoratedPairColored_trueSlotCount decorated

/--
[sixVertexLoopDecoratedPairBigrade_eq_configurationPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopPairBigrade.lean)
-/
@[path]
private lemma sixVertexLoopDecoratedPairBigrade_eq_configurationPair_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {decorated : SixVertexLoopDecoratedPair T left right} :
-- imply
  sixVertexLoopDecoratedPairBigrade decorated = sixVertexConfigurationPairBigrade decorated.1 := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopDecoratedPairBigrade_eq_configurationPair decorated

/--
[sixVertexLoopDecoratedPairBigrade_eq_colored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopPairBigrade.lean)
-/
@[path]
private lemma sixVertexLoopDecoratedPairBigrade_eq_colored_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {decorated : SixVertexLoopDecoratedPair T left right} :
-- imply
  sixVertexLoopDecoratedPairBigrade decorated = (fkColoredLoopPairingPairTotalC (sixVertexLoopDecoratedPairColored decorated), fkColoredTrueStrandSlotCount (sixVertexLoopDecoratedPairColored decorated)) := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopDecoratedPairBigrade_eq_colored decorated


-- created on 2026-10-23
