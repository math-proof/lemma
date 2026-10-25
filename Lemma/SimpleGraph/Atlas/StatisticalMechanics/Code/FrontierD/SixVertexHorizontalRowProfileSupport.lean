import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalRowProfileSupport.Part2
open Finset StatMech StatMech.FrontierD


/--
[sum_sixVertexHorizontalRowZeroCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalRowProfileSupport.lean)
-/
@[path]
private lemma sum_sixVertexHorizontalRowZeroCount_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T) :
-- imply
  (∑ j : Fin T.height, sixVertexHorizontalRowZeroCount horizontal j) = sixVertexHorizontalZeroCount horizontal := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexHorizontalRowZeroCount horizontal

/--
[sum_sixVertexHorizontalPairRowZeroProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalRowProfileSupport.lean)
-/
@[path]
private lemma sum_sixVertexHorizontalPairRowZeroProfile_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
-- imply
  (∑ j : Fin T.height, sixVertexHorizontalPairRowZeroProfile horizontal j) = sixVertexHorizontalZeroCount horizontal.1 + sixVertexHorizontalZeroCount horizontal.2 := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexHorizontalPairRowZeroProfile horizontal

/--
[sixVertexHorizontalRowZeroCount_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalRowProfileSupport.lean)
-/
@[path]
private lemma sixVertexHorizontalRowZeroCount_reflect_eq
  {T : EvenTorus}
  {j : Fin T.height}
-- given
  (horizontal : SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalRowZeroCount (sixVertexReflectHorizontalField horizontal) j = sixVertexHorizontalRowZeroCount horizontal j := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalRowZeroCount_reflect horizontal j

/--
[sixVertexSwitchHorizontalPair_rowZeroProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalRowProfileSupport.lean)
-/
@[path]
private lemma sixVertexSwitchHorizontalPair_rowZeroProfile_eq
  {T : EvenTorus}
-- given
  (mask : Fin T.width -> Bool)
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalPairRowZeroProfile (sixVertexSwitchHorizontalPair mask horizontal) = sixVertexHorizontalPairRowZeroProfile horizontal := by
-- proof
  apply StatMech.FrontierD.sixVertexSwitchHorizontalPair_rowZeroProfile mask horizontal

/--
[sixVertexReflectFirstHorizontalLayer_rowZeroProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalRowProfileSupport.lean)
-/
@[path]
private lemma sixVertexReflectFirstHorizontalLayer_rowZeroProfile_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalPairRowZeroProfile (sixVertexReflectFirstHorizontalLayer horizontal) = sixVertexHorizontalPairRowZeroProfile horizontal := by
-- proof
  apply StatMech.FrontierD.sixVertexReflectFirstHorizontalLayer_rowZeroProfile horizontal

/--
[sixVertexReflectSecondHorizontalLayer_rowZeroProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalRowProfileSupport.lean)
-/
@[path]
private lemma sixVertexReflectSecondHorizontalLayer_rowZeroProfile_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalPairRowZeroProfile (sixVertexReflectSecondHorizontalLayer horizontal) = sixVertexHorizontalPairRowZeroProfile horizontal := by
-- proof
  apply StatMech.FrontierD.sixVertexReflectSecondHorizontalLayer_rowZeroProfile horizontal

/--
[sixVertexSwapHorizontalLayers_rowZeroProfile](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalRowProfileSupport.lean)
-/
@[path]
private lemma sixVertexSwapHorizontalLayers_rowZeroProfile_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalPairRowZeroProfile (sixVertexSwapHorizontalLayers horizontal) = sixVertexHorizontalPairRowZeroProfile horizontal := by
-- proof
  apply StatMech.FrontierD.sixVertexSwapHorizontalLayers_rowZeroProfile horizontal

/--
[actualDeficitTokenHall_rowProfile_iff_capacity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalRowProfileSupport.lean)
-/
@[path]
private lemma actualDeficitTokenHall_rowProfile_iff_capacity_eq
  {T : EvenTorus}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)} :
-- imply
  SixVertexHorizontalActualDeficitTokenHall T sourceLeft sourceRight targetLeft targetRight (sixVertexHorizontalActualRowProfileSupport T sourceLeft sourceRight targetLeft targetRight) ↔ SixVertexHorizontalRowProfileResidualCapacity T sourceLeft sourceRight targetLeft targetRight := by
-- proof
  apply StatMech.FrontierD.actualDeficitTokenHall_rowProfile_iff_capacity T sourceLeft sourceRight targetLeft targetRight

/--
[configurationBigradeFibers_of_rowProfileResidualHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalRowProfileSupport.lean)
-/
@[path]
private lemma configurationBigradeFibers_of_rowProfileResidualHall_eq
  {T : EvenTorus}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
-- given
  (hHall : SixVertexHorizontalActualDeficitTokenHall T sourceLeft sourceRight targetLeft targetRight (sixVertexHorizontalActualRowProfileSupport T sourceLeft sourceRight targetLeft targetRight)) :
-- imply
  SixVertexConfigurationPairBigradeFiberDominates T sourceLeft sourceRight targetLeft targetRight := by
-- proof
  apply StatMech.FrontierD.configurationBigradeFibers_of_rowProfileResidualHall T sourceLeft sourceRight targetLeft targetRight hHall

/--
[configurationBigradeFibers_of_rowProfileResidualCapacity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalRowProfileSupport.lean)
-/
@[path]
private lemma configurationBigradeFibers_of_rowProfileResidualCapacity_eq
  {T : EvenTorus}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
-- given
  (hcapacity : SixVertexHorizontalRowProfileResidualCapacity T sourceLeft sourceRight targetLeft targetRight) :
-- imply
  SixVertexConfigurationPairBigradeFiberDominates T sourceLeft sourceRight targetLeft targetRight := by
-- proof
  apply StatMech.FrontierD.configurationBigradeFibers_of_rowProfileResidualCapacity T sourceLeft sourceRight targetLeft targetRight hcapacity


-- created on 2026-10-23
