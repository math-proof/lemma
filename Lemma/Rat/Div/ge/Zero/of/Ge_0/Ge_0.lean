import Lemma.Rat.GeDivS.of.Ge.Ge_0
import Lemma.Algebra.EqDiv0'0
open Algebra Rat


@[main]
private lemma main
  [GroupWithZero α]
  [PartialOrder α]
  [ZeroLEOneClass α]
  [PosMulReflectLT α]
  [MulPosStrictMono α]
  {a b : α}
-- given
  (h₀ : a ≥ 0)
  (h₁ : b ≥ 0) :
-- imply
  a / b ≥ 0 := by
-- proof
  have h := GeDivS.of.Ge.Ge_0 h₀ h₁
  simp only [EqDiv0'0] at h
  assumption


-- created on 2025-01-14
