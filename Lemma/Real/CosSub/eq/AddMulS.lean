import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Real.CosSub.eq.AddMulS |
| comm | Real.AddMulS.eq.CosSub |
-/
@[main, comm]
private lemma main
-- given
  (x y : ℝ) :
-- imply
  Real.cos (x - y) = Real.cos x * Real.cos y + Real.sin x * Real.sin y :=
-- proof
  Real.cos_sub x y


@[main, comm]
private lemma Comm
-- given
  (x y : ℝ) :
-- imply
  Real.cos (x - y) = Real.sin x * Real.sin y + Real.cos x * Real.cos y := by
-- proof
  rw [main]
  ring


-- created on 2020-11-19
-- updated on 2026-09-02
