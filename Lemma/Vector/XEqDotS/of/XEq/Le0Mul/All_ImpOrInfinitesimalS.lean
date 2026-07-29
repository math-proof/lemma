import Lemma.Hyperreal.XEqMulS.of.XEq.ImpOrInfinitesimalS
import Lemma.Vector.Dot
import Lemma.Vector.XEqSumS.of.XEq.Ge_0
open Hyperreal Vector


@[main]
private lemma main
  {a b x : List.Vector ℝ* n}
-- given
  (h_or : ∀ i : Fin n, ((b[i] → 0) ∨ x[i] → 0) → ((b[i] → 0) ∧ x[i] → 0))
  (h_pos : b * x ≥ 0)
  (h : a ≈ b) :
-- imply
  a @ x ≈ b @ x := by
-- proof
  rw [Dot.eq.SumMul, Dot.eq.SumMul]
  apply XEqSumS.of.XEq.Ge_0 h_pos
  refine Vector.XEq.of.All_XEqGetS.fin ?_
  intro i
  rw [GetMul.eq.MulGetS.fin a x i, GetMul.eq.MulGetS.fin b x i]
  exact XEqMulS.of.XEq.ImpOrInfinitesimalS (h_or i) (All_XEqGetS.of.XEq.fin h i)


@[main]
private lemma left
  {a b x : List.Vector ℝ* n}
-- given
  (h_or : ∀ i : Fin n, ((x[i] → 0) ∨ b[i] → 0) → ((x[i] → 0) ∧ b[i] → 0))
  (h_pos : x * b ≥ 0)
  (h : a ≈ b) :
-- imply
  x @ a ≈ x @ b := by
-- proof
  simp_rw [And.comm, Or.comm] at h_or
  rw [Dot.comm]
  conv_rhs =>
    rw [Dot.comm]
  exact main h_or (by rwa [← Mul.comm x b]) h


-- created on 2026-07-29
