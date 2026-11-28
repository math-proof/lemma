import Lemma.Random.ExpectCondMulVec.eq.MulVec_ExpectCond
import Initialize.Tactic.Attr.Basic
open Random


/--
The componentwise conditional expectation of a constant matrix–vector
product equals the matrix applied to the componentwise conditional
expectation of the vector.

| attributes | lemma |
| :---: | :---: |
| path | Random.ExpectCondDot.eq.Dot_ExpectCond |
| comm | Random.Dot_ExpectCond.eq.ExpectCondDot |
-/
@[path, comm]
private lemma main
  [MeasurableSpace Ω]
  [MeasurableSpace α] [StandardBorelSpace α] [Nonempty α]
  [Countable α] [MeasurableSingletonClass α]
  [MeasurableSpace γ]
  {π : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure π]
  {m k : ℕ}
  {a : Ω → α} {s : Ω → γ}
  {f : α → Fin k → ENNReal}
-- given
  (hf : ∀ p : Fin k, Measurable (fun x : α ↦ f x p))
  (A : Matrix (Fin m) (Fin k) ENNReal)
  («\sf{s}» : γ) :
-- imply
  (fun i ↦ 𝔼[a: π](Matrix.mulVec A (f a) i | s = «\sf{s}»)) =
    Matrix.mulVec A (fun p ↦ 𝔼[a: π](f a p | s = «\sf{s}»)) := by
-- proof
  apply ExpectCondMulVec.eq.MulVec_ExpectCond A hf


-- created on 2026-09-23
-- updated on 2026-11-28
