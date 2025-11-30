import Lemma.Tensor.Softmax.eq.Zero
open Tensor


@[main]
private lemma main
  [ExpGroup α]
-- given
  (h_s : s.length > 0)
  (h_0 : s[0] = 0)
  (X : Tensor α s) :
-- imply
  X.softmax 0 = 0 := by
-- proof
  match s with
  | [] =>
    contradiction
  | s₀ :: s =>
    subst h_0
    apply Softmax.eq.Zero


-- created on 2025-11-30
