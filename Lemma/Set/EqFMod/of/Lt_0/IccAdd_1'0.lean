import Lemma.Int.FMod.eq.Sub_MulFDiv
import Lemma.Algebra.EqSub.is.Eq_Add
import Lemma.Nat.Add
import Lemma.Int.Sub.eq.Zero
import Lemma.Set.FDiv.eq.Zero.of.Lt_0.IccAdd_1'0
open Algebra Set Nat Int


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h₀ : d < 0)
  (h₁ : n ∈ Icc (d + 1) 0) :
-- imply
  n.fmod d = n := by
-- proof
  rw [FMod.eq.Sub_MulFDiv]
  apply EqSub.of.Eq_Add
  rw [Add.comm]
  apply Eq_Add.of.EqSub
  rw [Sub.eq.Zero]
  have := FDiv.eq.Zero.of.Lt_0.IccAdd_1'0 h₀ h₁
  rw [this]
  simp


-- created on 2025-03-29
-- updated on 2025-03-30
