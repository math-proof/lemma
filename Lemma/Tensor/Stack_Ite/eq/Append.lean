import Lemma.Tensor.Stack.eq.AppendStackS
import Lemma.Tensor.Stack.of.All_Eq
open Tensor


@[main]
private lemma main
  {n m : ℕ}
-- given
  (f g : ℕ → Tensor α s) :
-- imply
  ([i < n + m] if (i : ℕ) < n then f i else g i) = [i < n] f i ++ [i < m] g (n + i) := calc
-- proof
  _ = [i < n] (if (i : ℕ) < n then f i else g i) ++ [i < m] (if n + (i : ℕ) < n then f (n + i) else g (n + i)) :=
    Stack.eq.AppendStackS (n := n) (j := m) (fun i => if i < n then f i else g i)
  _ = [i < n] f i ++ [i < m] g (n + i) := by
    apply congrArg₂ <;>
    ·
      apply Stack.of.All_Eq.fin
      grind


-- created on 2021-10-04
