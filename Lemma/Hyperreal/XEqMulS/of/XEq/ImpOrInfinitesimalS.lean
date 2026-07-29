import Lemma.Hyperreal.XEqMulS.of.XEq.XEq.ImpOrInfinitesimalS
open Hyperreal


@[main]
private lemma main
  {a b x : ℝ*}
-- given
  (h_or : ((b → 0) ∨ x → 0) → ((b → 0) ∧ x → 0))
  (h : a ≈ b) :
-- imply
  a * x ≈ b * x :=
-- proof
  XEqMulS.of.XEq.XEq.ImpOrInfinitesimalS h_or h (Setoid.refl _)


@[main]
private lemma left
  {a b x : ℝ*}
-- given
  (h_or : ((b → 0) ∨ x → 0) → ((b → 0) ∧ x → 0))
  (h : a ≈ b) :
-- imply
  x * a ≈ x * b := by
-- proof
  rw [mul_comm]
  conv_rhs =>
    rw [mul_comm]
  exact main h_or h


-- created on 2026-07-29
