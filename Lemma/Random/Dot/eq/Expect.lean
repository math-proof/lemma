import Lemma.Random.ExpectCondMulVec.eq.MulVec_ExpectCond
import Initialize.Tactic.Attr.Basic
open Random


/--
Multiplying a vector of conditional expectations by a constant matrix equals
taking conditional expectation of each entry of the matrix–vector product.

| attributes | lemma |
| :---: | :---: |
| path | Random.Dot.eq.Expect |
| comm | Random.Expect.eq.Dot |
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
  Matrix.mulVec A (fun p ↦ 𝔼[a: π](f a p | s = «\sf{s}»)) =
    (fun i ↦ 𝔼[a: π](Matrix.mulVec A (f a) i | s = «\sf{s}»)) := by
-- proof
  symm
  apply ExpectCondMulVec.eq.MulVec_ExpectCond A hf


-- created on 2023-04-07
-- updated on 2026-11-28
