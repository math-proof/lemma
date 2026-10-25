/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/InfiniteWord/OverlapFreeBinaryWord.lean -/


import Def.Combinatorics.InfiniteWord.OverlapFreeBinaryWord


namespace MetaMathlibExt

example : IsWordOverlap ([false, true, false, true, false] : List Bool) := by
  refine ⟨[false], [true], by simp, ?_⟩
  rfl

example : IsWordOverlap
    ([false, true, true, false, true, true, false, true] : List Bool) := by
  refine ⟨[false, true], [true], by simp, ?_⟩
  rfl

example : IsOverlapFreeBinaryWord [] := by
  simp [IsOverlapFreeBinaryWord, IsWordOverlap]

end MetaMathlibExt
