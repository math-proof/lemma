import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalDiagonalDeficit.Part2
open StatMech StatMech.FrontierD


/--
[natChoose_logConcave_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalDiagonalDeficit.lean)
-/
@[path]
private lemma natChoose_logConcave_of_pos_eq
  {n k : Nat}
-- given
  (hk : 0 < k) :
-- imply
  Nat.choose n (k - 1) * Nat.choose n (k + 1) <= Nat.choose n k * Nat.choose n k := by
-- proof
  apply StatMech.FrontierD.natChoose_logConcave_of_pos n k hk

/--
[sixVertexHorizontalProfileChooseCount_logConcave](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalDiagonalDeficit.lean)
-/
@[path]
private lemma sixVertexHorizontalProfileChooseCount_logConcave_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {profile : Option (SixVertexHorizontalCompletionProfile T)}
-- given
  (hpos : 0 < middle.val)
  (hlt : middle.val < T.width) :
-- imply
  sixVertexHorizontalProfileChooseCount (sixVertexHorizontalLowerSector middle hpos) profile * sixVertexHorizontalProfileChooseCount (sixVertexHorizontalUpperSector middle hlt) profile <= sixVertexHorizontalProfileChooseCount middle profile * sixVertexHorizontalProfileChooseCount middle profile := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalProfileChooseCount_logConcave middle hpos hlt profile

/--
[sixVertexHorizontalDiagonalProfileDeficit_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalDiagonalDeficit.lean)
-/
@[path]
private lemma sixVertexHorizontalDiagonalProfileDeficit_eq_zero_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {profile : Option (SixVertexHorizontalCompletionProfile T)}
-- given
  (hpos : 0 < middle.val)
  (hlt : middle.val < T.width) :
-- imply
  sixVertexHorizontalProfileDeficit (sixVertexHorizontalLowerSector middle hpos) (sixVertexHorizontalUpperSector middle hlt) middle middle (profile, profile) = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalDiagonalProfileDeficit_eq_zero middle hpos hlt profile

/--
[sixVertexHorizontalActualDeficitToken_profiles_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalDiagonalDeficit.lean)
-/
@[path]
private lemma sixVertexHorizontalActualDeficitToken_profiles_ne_eq
  {T : EvenTorus}
  {grade : Nat × Nat}
  {middle : Fin (T.width + 1)}
  {token : SixVertexHorizontalActualDeficitTokens T grade (sixVertexHorizontalLowerSector middle hpos) (sixVertexHorizontalUpperSector middle hlt) middle middle}
-- given
  (hpos : 0 < middle.val)
  (hlt : middle.val < T.width) :
-- imply
  token.1.1 ≠ token.1.2 := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalActualDeficitToken_profiles_ne middle hpos hlt token


-- created on 2026-10-23
