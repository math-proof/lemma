import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.MarkedStepInAMultiMarkedDyckPath.Part2
open MetaMathlibExt


namespace MetaMathlibExt

/--
[multiMarkedCountEq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MarkedStepInAMultiMarkedDyckPath.lean)
-/
@[path]
lemma multiMarkedCountEq
  {P : MultiMarkedDyckPath} :
-- imply
  multiMarkedCountE P.steps = multiMarkedCountVert P.steps :=
-- proof
  P.diagonal_endpoint

end MetaMathlibExt

namespace MetaMathlibExt

/--
[multiMarkedVertShifted_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MarkedStepInAMultiMarkedDyckPath.lean)
-/
@[path]
lemma multiMarkedVertShifted_eq
  {l : List MultiMarkedStep} :
-- imply
  multiMarkedCountVert l + multiMarkedShiftedIndexSum l =
    multiMarkedCountPlainN l + multiMarkedIndexSum l := by
-- proof
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    cases hd with
    | E =>
      simp only [multiMarkedCountVert, multiMarkedShiftedIndexSum,
        multiMarkedCountPlainN, multiMarkedIndexSum]
      exact ih
    | N =>
      simp only [multiMarkedCountVert, multiMarkedShiftedIndexSum,
        multiMarkedCountPlainN, multiMarkedIndexSum]
      omega
    | marked t h =>
      simp only [multiMarkedCountVert, multiMarkedShiftedIndexSum,
        multiMarkedCountPlainN, multiMarkedIndexSum]
      omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[multiMarkedSizeEq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MarkedStepInAMultiMarkedDyckPath.lean)
-/
@[path]
lemma multiMarkedSizeEq
  {P : MultiMarkedDyckPath} :
-- imply
  multiMarkedSize P.steps =
    multiMarkedCountPlainN P.steps + multiMarkedIndexSum P.steps := by
-- proof
  unfold multiMarkedSize
  have h := multiMarkedVertShifted_eq P.steps
  have he := multiMarkedCountEq P
  omega

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
