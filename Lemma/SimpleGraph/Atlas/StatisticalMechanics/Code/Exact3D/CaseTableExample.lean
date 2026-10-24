import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.CaseTableExample
open StatMech StatMech.Exact3D StatMech.Exact3D.CaseTableExample


/--
[boolTable_covers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CaseTableExample.lean)
-/
@[path]
private lemma boolTable_covers_eq :
-- imply
  RatInterval.CaseTable.Covers boolTable classify := by
-- proof
  apply StatMech.Exact3D.CaseTableExample.boolTable_covers

/--
[boolTable_sound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/CaseTableExample.lean)
-/
@[path]
private lemma boolTable_sound_eq :
-- imply
  RatInterval.CaseTable.Sound boolTable classify value := by
-- proof
  apply StatMech.Exact3D.CaseTableExample.boolTable_sound


-- created on 2026-10-23
