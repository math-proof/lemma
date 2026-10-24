import Mathlib
import sympy.Basic
import sympy.atlas.MathlibExtTest.NumberTheory.MultipleZeta.Index


namespace MetaMathlibExt.MultipleZeta

/--
[ofList_replicate](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/MultipleZeta/Index.lean)
-/
@[path]
private lemma ofList_replicate (n : ℕ) :
  FreeMonoid.ofList (List.replicate n false) =
    (FreeMonoid.of false) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, FreeMonoid.ofList_cons, ih, pow_succ']

end MetaMathlibExt.MultipleZeta


-- created on 2026-10-23
