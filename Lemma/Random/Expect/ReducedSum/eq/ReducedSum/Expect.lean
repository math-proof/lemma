import Mathlib.Probability.Independence.Integration
import Def.Probability.Moments.Variance
import Initialize.Tactic.Attr.Basic
open MeasureTheory


@[path]
private lemma main
  [MeasurableSpace Ω]
  [MeasurableSpace α]
  {π : Measure Ω}
  {x : Ω → α}
  {n : ℕ}
  {f : Fin n → α → ℝ}
-- given
  [PSpace π x]
  (hf : ∀ i, Integrable (f i) (π.map x)) :
-- imply
  𝔼[x: π](∑ i, f i x) = ∑ i, 𝔼[x: π](f i x) := by
-- proof
  simp only [Expectation.asRV_function, Expectation.ofRV, expectation_real]
  exact integral_finsetSum _ (fun i _ => hf i)


-- created on 2023-04-10
