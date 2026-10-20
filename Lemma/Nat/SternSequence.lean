import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.SternSequence
open MetaMathlibExt


/--
[stern_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SternSequence.lean)
-/
@[path]
private lemma stern_zero_eq
  :
-- imply
  sternSequence 0 = 0 := by
-- proof
  apply MetaMathlibExt.stern_zero

/--
[stern_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SternSequence.lean)
-/
@[path]
private lemma stern_one_eq
  :
-- imply
  sternSequence 1 = 1 := by
-- proof
  apply MetaMathlibExt.stern_one

/--
[stern_even](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SternSequence.lean)
-/
@[path]
private lemma stern_even_eq
  {n : Nat}
-- given
  (hn : 1 ≤ n) :
-- imply
  sternSequence (2 * n) = sternSequence n := by
-- proof
  apply MetaMathlibExt.stern_even n hn

/--
[stern_odd](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SternSequence.lean)
-/
@[path]
private lemma stern_odd_eq
  {n : Nat}
-- given
  (hn : 1 ≤ n) :
-- imply
  sternSequence (2 * n + 1) = sternSequence n + sternSequence (n + 1) := by
-- proof
  apply MetaMathlibExt.stern_odd n hn


-- created on 2026-10-20
