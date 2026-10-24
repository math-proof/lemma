import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexColoredVertexCrossFineRowProfile
open Finset StatMech StatMech.FrontierD


/--
[sixVertexHorizontalGaugeBit_coloredArrows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredVertexCrossFineRowProfile.lean)
-/
@[path]
private lemma sixVertexHorizontalGaugeBit_coloredArrows_eq
  {T : EvenTorus}
  {colored : FKColoredLoopPairing T}
  {v : T.Vertex} :
-- imply
  sixVertexHorizontalGaugeBit colored.arrows.horizontal v = !colored.color (v, .east) := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalGaugeBit_coloredArrows colored v

/--
[fkColoredVertexCrossTarget_eastColors_eq_or_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredVertexCrossFineRowProfile.lean)
-/
@[path]
private lemma fkColoredVertexCrossTarget_eastColors_eq_or_swap_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
  {v : T.Vertex}
-- given
  (mask : T.Vertex -> Bool)
  (hbond : FKColoredVertexCrossBondCoherent source mask) :
-- imply
  ((fkColoredVertexCrossTarget source mask hbond false).color (v, .east), (fkColoredVertexCrossTarget source mask hbond true).color (v, .east)) = ((source false).color (v, .east), (source true).color (v, .east)) \/ ((fkColoredVertexCrossTarget source mask hbond false).color (v, .east), (fkColoredVertexCrossTarget source mask hbond true).color (v, .east)) = ((source true).color (v, .east), (source false).color (v, .east)) := by
-- proof
  apply StatMech.FrontierD.fkColoredVertexCrossTarget_eastColors_eq_or_swap source mask hbond v

/--
[fkColoredVertexCrossTarget_rowZeroProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredVertexCrossFineRowProfile.lean)
-/
@[path]
private lemma fkColoredVertexCrossTarget_rowZeroProfile_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
-- given
  (mask : T.Vertex -> Bool)
  (hbond : FKColoredVertexCrossBondCoherent source mask) :
-- imply
  sixVertexHorizontalPairRowZeroProfile ((fkColoredVertexCrossTarget source mask hbond false).arrows.horizontal, (fkColoredVertexCrossTarget source mask hbond true).arrows.horizontal) = sixVertexHorizontalPairRowZeroProfile ((source false).arrows.horizontal, (source true).arrows.horizontal) := by
-- proof
  apply StatMech.FrontierD.fkColoredVertexCrossTarget_rowZeroProfile source mask hbond

/--
[fkColoredVertexCrossTarget_rowNontransitionProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredVertexCrossFineRowProfile.lean)
-/
@[path]
private lemma fkColoredVertexCrossTarget_rowNontransitionProfile_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
-- given
  (mask : T.Vertex -> Bool)
  (hbond : FKColoredVertexCrossBondCoherent source mask) :
-- imply
  sixVertexHorizontalPairRowNontransitionProfile ((fkColoredVertexCrossTarget source mask hbond false).arrows.horizontal, (fkColoredVertexCrossTarget source mask hbond true).arrows.horizontal) = sixVertexHorizontalPairRowNontransitionProfile ((source false).arrows.horizontal, (source true).arrows.horizontal) := by
-- proof
  apply StatMech.FrontierD.fkColoredVertexCrossTarget_rowNontransitionProfile source mask hbond

/--
[fkColoredVertexCrossTarget_boundedFineRowProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredVertexCrossFineRowProfile.lean)
-/
@[path]
private lemma fkColoredVertexCrossTarget_boundedFineRowProfile_eq
  {T : EvenTorus}
  {source : FKColoredLoopPairingPair T}
-- given
  (mask : T.Vertex -> Bool)
  (hbond : FKColoredVertexCrossBondCoherent source mask) :
-- imply
  sixVertexHorizontalPairBoundedFineRowProfile ((fkColoredVertexCrossTarget source mask hbond false).arrows.horizontal, (fkColoredVertexCrossTarget source mask hbond true).arrows.horizontal) = sixVertexHorizontalPairBoundedFineRowProfile ((source false).arrows.horizontal, (source true).arrows.horizontal) := by
-- proof
  apply StatMech.FrontierD.fkColoredVertexCrossTarget_boundedFineRowProfile source mask hbond


-- created on 2026-10-23
