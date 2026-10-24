import Mathlib
import sympy.Basic
import sympy.atlas.MathlibExtTest.Combinatorics.FractalSequenceTest


namespace MetaMathlibExt

/--
[triangle_strict](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/FractalSequenceTest.lean)
-/
@[path]
private lemma triangle_strict : StrictMono triangle := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [triangle_succ]
  omega

end MetaMathlibExt


-- created on 2026-10-23
