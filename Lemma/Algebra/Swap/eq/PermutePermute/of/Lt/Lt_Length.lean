import Lemma.Algebra.LengthPermute.eq.Length
import Lemma.Algebra.Swap.eq.PermutePermute.of.Lt
import Lemma.Algebra.CoeSub.eq.SubCoeS.of.Gt
import Lemma.Algebra.Sub.eq.NegSub
import Lemma.Algebra.ValSub.eq.SubValS.of.Gt
open Algebra


@[main]
private lemma main
  {s : List α}
  {i j : ℕ}
-- given
  (h₀ : j < s.length)
  (h₁ : i < j) :
-- imply
  let d := j - i
  s.swap i j = (s.permute ⟨i, by linarith⟩ (d - 1)).permute ⟨j, by simp_all [LengthPermute.eq.Length]⟩ (-d) := by
-- proof
  let i : Fin s.length := ⟨i, by linarith⟩
  let j : Fin s.length := ⟨j, h₀⟩
  have h_lt : i < j := by
    simpa [i, j]
  have := Swap.eq.PermutePermute.of.Lt h_lt
  simp_all [i, j]
  rw [CoeSub.eq.SubCoeS.of.Gt (by assumption)]
  rw [ValSub.eq.SubValS.of.Gt (by simp_all)]
  rw [NegSub.eq.Sub]
  rw [CoeSub.eq.SubCoeS.of.Gt (by assumption)]
  rw [NegSub.eq.Sub]


-- created on 2025-06-21
