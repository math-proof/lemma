import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.MarkedStepInAMultiMarkedDyckPath
open MetaMathlibExt


/--
[multiMarkedCountEq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MarkedStepInAMultiMarkedDyckPath.lean)
-/
@[path]
private lemma multiMarkedCountEq_eq
  {P : MultiMarkedDyckPath} :
-- imply
  multiMarkedCountE P.steps = multiMarkedCountVert P.steps := by
-- proof
  apply MetaMathlibExt.multiMarkedCountEq P

/--
[multiMarkedVertShifted_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MarkedStepInAMultiMarkedDyckPath.lean)
-/
@[path]
private lemma multiMarkedVertShifted_eq_eq
  {l : List MultiMarkedStep} :
-- imply
  multiMarkedCountVert l + multiMarkedShiftedIndexSum l =
    multiMarkedCountPlainN l + multiMarkedIndexSum l := by
-- proof
  apply MetaMathlibExt.multiMarkedVertShifted_eq l

/--
[multiMarkedSizeEq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MarkedStepInAMultiMarkedDyckPath.lean)
-/
@[path]
private lemma multiMarkedSizeEq_eq
  {P : MultiMarkedDyckPath} :
-- imply
  multiMarkedSize P.steps =
    multiMarkedCountPlainN P.steps + multiMarkedIndexSum P.steps := by
-- proof
  apply MetaMathlibExt.multiMarkedSizeEq P


-- created on 2026-10-20
