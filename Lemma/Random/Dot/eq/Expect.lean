import Lemma.Random.Expect_CondDot.eq.Dot_Expect_Cond
import sympy.stats.joint_rv
import sympy.stats.symbolic_multivariate_probability
import sympy.matrices.expressions.matmul
open Random Tensor


/--
A constant matrix–vector product (@ / Dot.dot) pulls through a
conditional expectation, constant-first orientation.

Python: Random.Dot.eq.Expect.

| attributes | lemma |
| :---: | :---: |
| main | Random.Dot.eq.Expect |
| comm | Random.Expect.eq.Dot |
-/
@[main, comm]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure γ]
  [Countable α] [MeasurableSingletonClass α]
  {π : MeasureTheory.Measure Ω} {m k : ℕ}
  {a : Ω → α} {s : Ω → γ}
  {f : α → Tensor ENNReal [k]}
-- given
  (hP : PSpace π (a, s))
  (A : Tensor ENNReal [m, k])
  (hf : ∀ p : Fin k, Measurable (fun x : α ↦ (f x)[p].item))
  («s.bvar» : γ) :
-- imply
  A @ 𝔼[a: π](f a | s = «s.bvar») =
    𝔼[a: π](A @ f a | s = «s.bvar») :=
-- proof
  (Expect_CondDot.eq.Dot_Expect_Cond (hP := hP) (A := A)
    (hf := hf) («s.bvar» := «s.bvar»)).symm


-- created on 2026-09-26
