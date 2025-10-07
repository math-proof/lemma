import Lemma.Bool.Imp.of.Iff
import Lemma.Bool.Imp.is.Bool.eq.MulBoolS
import Lemma.Algebra.Mul
open Algebra Bool


@[main]
private lemma main
  [Decidable p]
  [Decidable q]
-- given
  (h : p ↔ q) :
-- imply
  Bool.toNat p = Bool.toNat q := by
-- proof
  have := Imp.of.Iff h
  have h₀ := Bool.eq.MulBoolS.of.Imp this
  have := Imp.of.Iff h.symm
  have h₁ := Bool.eq.MulBoolS.of.Imp this
  rw [Mul.comm] at h₁
  exact Eq.trans h₀ h₁.symm


-- created on 2025-04-12
