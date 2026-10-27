import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalOffDiagonalTwoCycleMatching
open StatMech StatMech.FrontierD


/--
[sixVertexHorizontalOffDiagonalTwoCycleSupport_profiles_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalOffDiagonalTwoCycleMatching.lean)
-/
@[path]
private lemma sixVertexHorizontalOffDiagonalTwoCycleSupport_profiles_ne_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {hmiddle_pos : 0 < middle.val}
  {hmiddle_lt : middle.val < T.width} :
-- imply
  forall grade (source : SixVertexHorizontalActualDeficitTokens T grade (sixVertexHorizontalLowerSector middle hmiddle_pos) (sixVertexHorizontalUpperSector middle hmiddle_lt) middle middle), Not (source.1.1 = source.1.2) := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalOffDiagonalTwoCycleSupport_profiles_ne

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_offDiagonalTwoCycleMatching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalOffDiagonalTwoCycleMatching.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_offDiagonalTwoCycleMatching_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hmatching : SixVertexHorizontalOffDiagonalTwoCycleMatching T middle hmiddle_pos hmiddle_lt) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_offDiagonalTwoCycleMatching T middle hmiddle_pos hmiddle_lt hmatching

/--
[sixVertexSectorTrace_logConcave_of_offDiagonalTwoCycleMatching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalOffDiagonalTwoCycleMatching.lean)
-/
@[path]
private lemma sixVertexSectorTrace_logConcave_of_offDiagonalTwoCycleMatching_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {c : Real}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hc : 2 <= c)
  (hmatching : SixVertexHorizontalOffDiagonalTwoCycleMatching T middle hmiddle_pos hmiddle_lt) :
-- imply
  Matrix.trace (sixVertexSectorTransfer T.width (middle.val - 1) c ^ T.height) * Matrix.trace (sixVertexSectorTransfer T.width (middle.val + 1) c ^ T.height) <= Matrix.trace (sixVertexSectorTransfer T.width middle.val c ^ T.height) ^ 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTrace_logConcave_of_offDiagonalTwoCycleMatching T middle hmiddle_pos hmiddle_lt hc hmatching


-- created on 2026-10-23
