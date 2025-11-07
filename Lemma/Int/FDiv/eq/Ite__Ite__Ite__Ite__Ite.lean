import Lemma.Bool.BFn_Ite.is.Imp.Imp
import Lemma.Int.FDiv.eq.Div.of.Ge_0
import Lemma.Bool.NotAnd.is.OrNotS
import Lemma.Nat.NotGe.is.Lt
import Lemma.Bool.Eq_Ite.of.Cond.NotAnd.Eq
import Lemma.Bool.IffAndSAnd
import Lemma.Nat.Gt.Lt.is.False
import Lemma.Bool.Iff_True.of.Cond
import Lemma.Int.Sub.eq.Add_Neg
import Lemma.Nat.Eq.is.False.of.Lt
import Lemma.Nat.Gt.is.False.of.Lt
import Lemma.Nat.Sub.eq.AddNeg
import Lemma.Int.SubNeg
import Lemma.Int.FDiv.eq.Ite.of.Lt_0
import Lemma.Int.FDiv.eq.Ite__Ite.of.Lt_0
open Bool Int Nat


@[main]
private lemma main
  {n d : ℤ} :
-- imply
  n // d =
    if n ≥ 0 ∧ d ≥ 0 then
      n / d
    else if n > 0 ∧ d < 0 then
      -((n - 1) / -d + 1)
    else if n < 0 ∧ d = 0 then
      0
    else if n < 0 ∧ d > 0 then
      -((-n - 1) / d + 1)
    else
      -n / -d := by
-- proof
  apply BFn_Ite.of.Imp.Imp
  intro ⟨_, h⟩
  apply FDiv.eq.Div.of.Ge_0 (n := n) h
  rw [NotAnd.is.OrNotS]
  rw [NotGe.is.Lt, NotGe.is.Lt]
  intro h_Or
  cases h_Or with
  | inl h_Lt_0 =>
    apply Eq_Ite.of.Cond.NotAnd.Eq h_Lt_0
    rw [IffAndSAnd]
    rw [Gt.Lt.is.False]
    simp
    have := Iff_True.of.Cond h_Lt_0
    simp [this]
    rw [Add_Neg.eq.Sub]
    rw [SubNeg.comm]
    apply FDiv.eq.Ite__Ite.of.Lt_0 h_Lt_0
  | inr h_Lt_0 =>
    have := Iff_True.of.Cond h_Lt_0
    simp [this]
    have := Eq.is.False.of.Lt h_Lt_0
    simp [this]
    have := Gt.is.False.of.Lt h_Lt_0
    simp [this]
    rw [AddNeg.eq.Sub]
    apply FDiv.eq.Ite.of.Lt_0 h_Lt_0


-- created on 2025-03-21
-- updated on 2025-03-27
