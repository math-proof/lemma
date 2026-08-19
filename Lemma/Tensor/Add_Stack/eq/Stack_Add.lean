import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetAdd.eq.AddGetS
open Tensor


@[main]
private lemma main
  [Add α]
-- given
  (g : Tensor α (m :: s))
  (f : ℕ → Tensor α s) :
-- imply
  g + [i < m] f i = [i < m] (id (α := Tensor α s) g[i] + f i) := by
-- proof
  apply Eq.of.All_EqGetS
  intro i
  rw [EqGetStack]
  rw [GetAdd.eq.AddGetS]
  rw [EqGetStack.fun]
  rfl


-- created on 2018-04-04
-- updated on 2026-08-19
