import Lemma.Tensor.Sum.eq.Zero
import sympy.tensor.tensor
open Tensor


@[main]
private lemma main
  [Add α] [Zero α]
-- given
  (h_s : s.length > 0)
  (h_0 : s[0] = 0)
  (X : Tensor α s) :
-- imply
  X.sum 0 = 0 := by
-- proof
  match s with
  | [] =>
    contradiction
  | s₀ :: s =>
    simp
    subst h_0
    apply Sum.eq.Zero


-- created on 2025-11-15
