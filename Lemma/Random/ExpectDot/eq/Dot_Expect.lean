import Lemma.Random.ExpectMulVec.eq.MulVec_Expect
import Initialize.Tactic.Attr.Basic
open Random


/--
The componentwise expectation of a constant matrix–vector product equals
the matrix applied to the componentwise expectation of the vector.

| attributes | lemma |
| :---: | :---: |
| path | Random.ExpectDot.eq.Dot_Expect |
| comm | Random.Dot_Expect.eq.ExpectDot |
-/
@[path, comm]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure α]
  [Countable α] [MeasurableSingletonClass α]
  {π : MeasureTheory.Measure Ω} {m k : ℕ}
  {a : Ω → α}
  {f : α → Fin k → ENNReal}
-- given
  (hP : SinglePSpace π a)
  (hf : ∀ p : Fin k, Measurable (fun x : α ↦ f x p))
  (A : Matrix (Fin m) (Fin k) ENNReal) :
-- imply
  (fun i ↦ 𝔼[a: π](Matrix.mulVec A (f a) i)) =
    Matrix.mulVec A (fun p ↦ 𝔼[a: π](f a p)) := by
-- proof
  apply ExpectMulVec.eq.MulVec_Expect hP A hf


-- created on 2023-04-07
-- updated on 2026-11-28
