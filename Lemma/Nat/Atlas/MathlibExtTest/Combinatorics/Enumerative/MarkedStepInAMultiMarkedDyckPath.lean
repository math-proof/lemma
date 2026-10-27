import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.Combinatorics.Enumerative.MarkedStepInAMultiMarkedDyckPath.Part2


namespace MetaMathlibExt

/--
[sourceExamplePath_unmarkedTail](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/MarkedStepInAMultiMarkedDyckPath.lean)
-/
@[path]
private lemma sourceExamplePath_unmarkedTail : sourceExamplePath.HasUnmarkedTail := by
  intro h
  obtain ⟨t, ht, hmem⟩ := h
  have htail : multiMarkedTrailingVert sourceExamplePath.steps = [.N] := rfl
  rw [htail] at hmem
  simp at hmem

end MetaMathlibExt


-- created on 2026-10-23
