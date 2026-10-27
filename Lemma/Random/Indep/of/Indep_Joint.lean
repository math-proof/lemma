import Mathlib.Probability.Independence.Basic
import Syntax.Probability.JointRv.Part6
import Initialize.Tactic.Attr.Basic
open ProbabilityTheory MeasureTheory


/--
If a random variable `x` is independent of a joint random variable `(y, z)`, then it is
independent of the first component `y`. In sympy this is the lemma
`Random.Indep.of.Indep_Joint`, written as `Equal(x | y & z, x) → Equal(x | y, x)`: the
conditional `ℙ(x | y & z) = ℙ(x)` (independence of `x` from the pair) entails the
marginal conditional `ℙ(x | y) = ℙ(x)`.

The proof is a direct application of `IndepFun.comp`: independence of `x` from `(y, z)`
is preserved under post-composing the second argument with the measurable projection
`Prod.fst`, and `Prod.fst ∘ (y, z) = y`. No density / `SinglePSpace` assumptions are needed —
independence is a σ-algebra property.
-/
@[path]
private lemma fst
  {Ω α β γ : Type*}
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β] [ReferenceMeasure γ]
  {π : Measure Ω}
  {x : Ω → α} {y : Ω → β} {z : Ω → γ}
-- given
  (h : x ⟂ᵢ[π] (y, z)) :
-- imply
  x ⟂ᵢ[π] y :=
-- proof
  h.comp measurable_id measurable_fst


/--
If a random variable `x` is independent of a joint random variable `(y, z)`, then it is
independent of the second component `z` (the `wrt = 1` case of the sympy lemma).
-/
@[path]
private lemma snd
  {Ω α β γ : Type*}
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β] [ReferenceMeasure γ]
  {π : Measure Ω}
  {x : Ω → α} {y : Ω → β} {z : Ω → γ}
-- given
  (h : x ⟂ᵢ[π] (y, z)) :
-- imply
  x ⟂ᵢ[π] z :=
-- proof
  h.comp measurable_id measurable_snd


-- created on 2020-12-13
-- updated on 2026-10-26
