import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.Combinatorics.Enumerative.RisingDiagonalSequence


namespace MetaMathlibExt

/--
[constTriangle_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/RisingDiagonalSequence.lean)
-/
@[path]
private lemma constTriangle_mem :
  IsBinaryBinomialInterpolatedTriangle constTriangle 1 1 (1 / 2) (1 / 2) := by
  refine ⟨by norm_num, by norm_num, rfl, rfl, fun _ _ => by
    simp only [constTriangle]
    norm_num, fun _ _ _ _ => by
    simp only [constTriangle]
    norm_num⟩

end MetaMathlibExt


-- created on 2026-10-23
