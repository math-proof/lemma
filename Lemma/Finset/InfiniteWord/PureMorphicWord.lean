import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.InfiniteWord.PureMorphicWord
open MetaMathlibExt


/--
[morphExtend_append](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/PureMorphicWord.lean)
-/
@[path]
private lemma morphExtend_append_eq
  {f : A → List A}
  {u v : List A} :
-- imply
  morphExtend f (u ++ v) = morphExtend f u ++ morphExtend f v := by
-- proof
  apply MetaMathlibExt.morphExtend_append f u v

/--
[morphIterate_length_of_uniform](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/PureMorphicWord.lean)
-/
@[path]
private lemma morphIterate_length_of_uniform_eq
  {k : Nat}
  {f : A → List A}
  {n : Nat}
  {w : List A}
-- given
  (hlen : ∀ x, (f x).length = k) :
-- imply
  (morphIterate f n w).length = k ^ n * w.length := by
-- proof
  apply MetaMathlibExt.morphIterate_length_of_uniform hlen n w


-- created on 2026-10-20
