import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.InfiniteWord.PureMorphicWord
open MetaMathlibExt


namespace MetaMathlibExt

/--
[morphIterate_length_of_uniform](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/PureMorphicWord.lean)
-/
@[path]
lemma morphIterate_length_of_uniform
  {k : Nat}
  {f : A → List A}
  {n : Nat}
  {w : List A}
-- given
  (hlen : ∀ x, (f x).length = k) :
-- imply
  (morphIterate f n w).length = k ^ n * w.length := by
-- proof
  have hext : ∀ v : List A, (morphExtend f v).length = k * v.length := by
    intro v
    induction v with
    | nil => rfl
    | cons x xs ih =>
      change (f x ++ morphExtend f xs).length = _
      rw [List.length_append, ih, hlen, List.length_cons, Nat.mul_succ, Nat.add_comm]
  induction n with
  | zero => simp [morphIterate]
  | succ n ih =>
    rw [morphIterate, hext, ih, Nat.pow_succ]
    ac_rfl

end MetaMathlibExt

/--
[morphExtend_append](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/PureMorphicWord.lean)
-/
@[path]
lemma morphExtend_append
  {f : A → List A}
  {u v : List A} :
-- imply
  morphExtend f (u ++ v) = morphExtend f u ++ morphExtend f v := by
-- proof
  induction u with
  | nil => rfl
  | cons b bs hb =>
    have e1 : morphExtend f ((b :: bs) ++ v)
      = f b ++ morphExtend f (bs ++ v) := rfl
    have e2 : morphExtend f (b :: bs)
      = f b ++ morphExtend f bs := rfl
    rw [e1, e2, hb, List.append_assoc]



-- created on 2026-10-20
-- updated on 2026-10-26
