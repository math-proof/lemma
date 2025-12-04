import sympy.Basic
import sympy.tensor.functions

/--
自然语言论述：[flash_attn](http://myhz0606.com/article/flash_attn)
-/
@[main]
private lemma main
  [NeZero s.prod]
  [LT α] [DecidableLT α]
  [ExpPos α]
  [Log α]
-- given
  (X : Tensor α s)
  (d : ℕ) :
-- imply
  log (X.softmax d) = X - (X.max d).keepdim - log ((exp (X - (X.max d).keepdim)).sum d).keepdim := by
-- proof
  sorry


-- created on 2025-12-03
