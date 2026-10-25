import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexLoopLexUnitFineRelation
open StatMech StatMech.FrontierD


/--
[sixVertexLoopLexUnitFineRelated_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopLexUnitFineRelation.lean)
-/
@[path]
private lemma sixVertexLoopLexUnitFineRelated_target_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T}
  {source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hunit : SixVertexLoopDecoratedLexComponentIsUnit middle hmiddle_pos hmiddle_lt source.1) :
-- imply
  SixVertexLoopLexUnitFineRelated middle hmiddle_pos hmiddle_lt profile source (sixVertexLoopDecoratedUnitTransferFineTarget middle hmiddle_pos hmiddle_lt profile source hunit) := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopLexUnitFineRelated_target middle hmiddle_pos hmiddle_lt profile source hunit

/--
[sixVertexLoopLexUnitFineRelated_iff_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopLexUnitFineRelation.lean)
-/
@[path]
private lemma sixVertexLoopLexUnitFineRelated_iff_eq_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T}
  {source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile}
  {target : SixVertexLoopDecoratedPairFineProfileFiber T middle middle profile}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hunit : SixVertexLoopDecoratedLexComponentIsUnit middle hmiddle_pos hmiddle_lt source.1) :
-- imply
  SixVertexLoopLexUnitFineRelated middle hmiddle_pos hmiddle_lt profile source target ↔ target = sixVertexLoopDecoratedUnitTransferFineTarget middle hmiddle_pos hmiddle_lt profile source hunit := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopLexUnitFineRelated_iff_eq middle hmiddle_pos hmiddle_lt profile source target hunit

/--
[sixVertexLoopLexUnitFineRelated_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopLexUnitFineRelation.lean)
-/
@[path]
private lemma sixVertexLoopLexUnitFineRelated_nonempty_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T}
  {source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hunit : SixVertexLoopDecoratedLexComponentIsUnit middle hmiddle_pos hmiddle_lt source.1) :
-- imply
  (Finset.univ.filter (SixVertexLoopLexUnitFineRelated middle hmiddle_pos hmiddle_lt profile source)).Nonempty := by
-- proof
  apply StatMech.FrontierD.sixVertexLoopLexUnitFineRelated_nonempty middle hmiddle_pos hmiddle_lt profile source hunit

/--
[card_sixVertexLoopLexUnitFineRelated_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexLoopLexUnitFineRelation.lean)
-/
@[path]
private lemma card_sixVertexLoopLexUnitFineRelated_eq_one_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {profile : SixVertexHorizontalBoundedFineRowProfile T}
  {source : SixVertexLoopDecoratedPairFineProfileFiber T (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) profile}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hunit : SixVertexLoopDecoratedLexComponentIsUnit middle hmiddle_pos hmiddle_lt source.1) :
-- imply
  (Finset.univ.filter (SixVertexLoopLexUnitFineRelated middle hmiddle_pos hmiddle_lt profile source)).card = 1 := by
-- proof
  apply StatMech.FrontierD.card_sixVertexLoopLexUnitFineRelated_eq_one middle hmiddle_pos hmiddle_lt profile source hunit


-- created on 2026-10-23
