import Lemma.Random.ExpectCondDot.eq.Dot_ExpectCond
open Random


/--
A constant matrix–vector product (@ / Dot.dot) pulls through a
conditional expectation, constant-first orientation.

Python: Random.Dot.eq.Expect.

| attributes | lemma |
| :---: | :---: |
| path | Random.Dot.eq.Expect |
| comm | Random.Expect.eq.Dot |
-/
@[path, comm]
private lemma main
  [MeasurableSpace Ω]
  [MeasurableSpace α]
  [Countable α] [MeasurableSingletonClass α]
  {π : MeasureTheory.Measure Ω} {m k : ℕ}
  {a : Ω → α} {s : Ω → γ}
  {f : α → Tensor ENNReal [k]}
-- given
  (A : Tensor ENNReal [m, k])
  (hf : ∀ p : Fin k, Measurable (fun x : α ↦ (f x)[p].item))
  («s.bvar» : γ) :
-- imply
  A @ 𝔼[a: π](f a | s = «s.bvar») =
    𝔼[a: π](A @ f a | s = «s.bvar») :=
-- proof
  (ExpectCondDot.eq.Dot_ExpectCond (A := A)
    (hf := hf) («s.bvar» := «s.bvar»)).symm


-- created on 2023-04-07
