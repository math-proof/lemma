import Lemma.Real.Gt0Cos.of.In_Ioc
import Lemma.Real.Lt0Cos.of.In_Ico
import Lemma.Set.Ge.of.In_Icc
import Lemma.Set.In_Icc.is.Le.Le
import Lemma.Set.In_Ico.of.In_Icc.Lt
import Lemma.Set.In_Ioc.of.In_Icc.Gt
import Lemma.Set.Le.of.In_Icc
open Real Set


@[main]
private lemma main
  {x : ℝ}
-- given
  (h₁ : x ∈ Icc 0 π)
  (h₀ : cos x = 0) :
-- imply
  x = π / 2 := by
-- proof
  obtain hlt | heq | hgt := lt_trichotomy x (π / 2)
  ·
    have hIcc := In_Icc.of.Le.Le (Ge.of.In_Icc h₁) (le_of_lt hlt)
    have hcos := Lt0Cos.of.In_Ico (In_Ico.of.In_Icc.Lt hIcc hlt)
    linarith
  ·
    exact heq
  ·
    have hIcc := In_Icc.of.Le.Le (le_of_lt hgt) (Le.of.In_Icc h₁)
    have hcos := Gt0Cos.of.In_Ioc (In_Ioc.of.In_Icc.Gt hgt hIcc)
    linarith


-- created on 2018-06-23
-- updated on 2026-08-03
