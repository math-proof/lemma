import Mathlib
import sympy.Basic
import sympy.atlas.Probability.Condorcet
open MetaMathlibExt


/--
[condorcet_jury_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Condorcet.lean)
-/
@[path]
private lemma condorcet_jury_theorem_eq
  [MeasurableSpace Ω]
  {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
  {X : ℕ → Ω → Bool}
  {p : ENNReal}
-- given
  (hp : 1 / 2 < p)
  (hp2 : p < 1)
  (hmeas : ∀ i, Measurable (X i))
  (hmarg : ∀ i, μ {ω | X i ω = true} = p)
  (hindep : ∀ s : Finset ℕ, s.Nonempty → μ (s.inf fun i => {ω | X i ω = true}) = s.prod fun i => μ {ω | X i ω = true}) :
-- imply
  Filter.Tendsto
    (fun n => μ {ω | n / 2 < (Finset.filter (fun i => X i ω = true) (Finset.range n)).card})
    Filter.atTop (nhds 1) ∧
    ∀ n : ℕ, Odd n → 1 < n →
    p < μ {ω | n / 2 < (Finset.filter (fun i => X i ω = true) (Finset.range n)).card} := by
-- proof
  apply MetaMathlibExt.condorcet_jury_theorem X p hp hp2 hmeas hmarg hindep

/--
[condorcet_jury_theorem_of_iIndepFun](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Condorcet.lean)
-/
@[path]
private lemma condorcet_jury_theorem_of_iIndepFun_eq
  [MeasurableSpace Ω]
  {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
  {X : ℕ → Ω → Bool}
  {p : ENNReal}
-- given
  (hp : 1 / 2 < p)
  (hp2 : p < 1)
  (hmeas : ∀ i, Measurable (X i))
  (hmarg : ∀ i, μ {ω | X i ω = true} = p)
  (hindep : ProbabilityTheory.iIndepFun X μ) :
-- imply
  Filter.Tendsto
    (fun n => μ {ω | n / 2 < (Finset.filter (fun i => X i ω = true) (Finset.range n)).card})
    Filter.atTop (nhds 1) ∧
    ∀ n : ℕ, Odd n → 1 < n →
    p < μ {ω | n / 2 < (Finset.filter (fun i => X i ω = true) (Finset.range n)).card} := by
-- proof
  apply MetaMathlibExt.condorcet_jury_theorem_of_iIndepFun X p hp hp2 hmeas hmarg hindep


-- created on 2026-10-20
