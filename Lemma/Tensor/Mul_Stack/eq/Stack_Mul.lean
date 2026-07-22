import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetMul.eq.MulGetS
open Tensor


@[main]
private lemma main
  [Mul α]
-- given
  (g : Tensor α (n :: s))
  (f : ℕ → Tensor α s) :
-- imply
  g * [i < n] f i = [i < n] (g[i] * f i) := by
-- proof
  apply Eq.of.All_EqGetS
  intro i
  rw [EqGetStack.fn]
  rw [GetMul.eq.MulGetS]
  rw [EqGetStack]
  rfl


@[main]
private lemma fin
  [Mul α]
-- given
  (g : Tensor α (n :: s))
  (f : Fin n → Tensor α s) :
-- imply
  g * [i < n] f i = [i < n] (g[i] * f i) := by
-- proof
  if h : n = 0 then
    subst h
    apply Eq.of.All_EqGetS.fin
    intro t
    have h_t := t.isLt
    simp at h_t
  else
    have := main g (fun i => if h_i : i < n then f ⟨i, by grind⟩ else f ⟨0, by grind⟩)
    simp at this
    grind



-- created on 2025-07-20
