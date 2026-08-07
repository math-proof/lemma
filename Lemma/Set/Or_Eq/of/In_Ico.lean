import Lemma.Finset.Insert_Ico.eq.Ico_Add_1
import Lemma.Set.EqIcoS
import Lemma.Set.In_Insert.is.Eq.ou.In
import Lemma.Set.In_Ico.is.Le.Lt
open Finset Set


@[main]
private lemma main
  {e a b : ℤ}
-- given
  (h₁ : e ∈ Set.Ico a (b + 1)) :
-- imply
  e ∈ Set.Ico a b ∨ e = b := by
-- proof
  have h₀ : a ≤ b := by
    obtain ⟨_, h_lt⟩ := Le.Lt.of.In_Ico h₁
    linarith
  have h_fin := Insert_Ico.eq.Ico_Add_1 h₀
  simp only [EqIcoS] at h₁
  rw [← h_fin] at h₁
  rw [Finset.coe_insert] at h₁
  have h := (Eq.ou.In.of.In_Insert h₁).symm
  rwa [← EqIcoS (i := a) (n := b)] at h


-- created on 2018-04-26
