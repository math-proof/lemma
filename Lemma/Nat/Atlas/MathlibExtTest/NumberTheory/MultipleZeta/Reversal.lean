import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.NumberTheory.MultipleZeta.Reversal


namespace MetaMathlibExt.MultipleZeta

/--
[oneEntryIndex_admissible](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/MultipleZeta/Reversal.lean)
-/
@[path]
private lemma oneEntryIndex_admissible :
  oneEntryIndex.IsIncreasingAdmissible := by
  simp [Index.IsIncreasingAdmissible, IsAdmissible, Index.entries,
    oneEntryIndex]

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[twoEntryIndex_admissible](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/MultipleZeta/Reversal.lean)
-/
@[path]
private lemma twoEntryIndex_admissible :
  twoEntryIndex.IsIncreasingAdmissible := by
  simp [Index.IsIncreasingAdmissible, IsAdmissible, Index.entries,
    twoEntryIndex]

end MetaMathlibExt.MultipleZeta


-- created on 2026-10-23
