import Mathlib
import sympy.Basic
open MeasureTheory ProbabilityTheory Filter


/--
[second_Borel_Cantelli](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/BorelCantelliSecond.lean)
-/
@[path]
lemma second_Borel_Cantelli
  {m0 : MeasurableSpace Ω}
  {μ : Measure Ω}
  {A : ℕ → Set Ω}
-- given
  (hm : ∀ n, MeasurableSet (A n))
  (hindep : iIndepSet A μ)
  (hsum : ∑' n, μ (A n) = ⊤) :
-- imply
  μ (limsup A atTop) = 1 :=
-- proof
  measure_limsup_eq_one hm hindep hsum


-- created on 2026-10-23
