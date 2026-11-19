import Mathlib.Probability.Independence.Integration
import Def.Probability.Moments.Variance
import Theorem.Probability.SymbolicProbability
import Initialize.Tactic.Attr.Basic
open MeasureTheory


/--
Additivity of expectation:
\(\mathbb{E}_{\pi}(f(x)) + \mathbb{E}_{\pi}(g(x)) = \mathbb{E}_{\pi}(f(x) + g(x))
\)
for integrable `f` and `g`.

| attributes | lemma |
| :---: | :---: |
| path | Random.AddExpectS.eq.Expect_Add.of.Integrable.Integrable |
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [MeasurableSpace α]
  {π : Measure Ω}
  {x : Ω → α} [PSpace π x]
  {f g : α → ℝ}
-- given
  (hf : Integrable f (π.map x))
  (hg : Integrable g (π.map x)) :
-- imply
  𝔼[x: π](f x) + 𝔼[x: π](g x) = 𝔼[x: π](f x + g x) := by
-- proof
  simp only [Expectation.asRV_function, Expectation.ofRV, expectation_real]
  rw [integral_add hf hg]


-- created on 2023-04-13
-- updated on 2026-11-17
