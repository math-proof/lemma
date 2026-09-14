import Mathlib.Probability.Independence.Basic
import sympy.stats.joint_rv
import sympy.Basic
open ProbabilityTheory MeasureTheory


/--
If a random variable `x` is independent of a joint random variable `(y, z)`, then it is
independent of the first component `y`. In sympy this is the lemma
`Random.Indep.of.Indep_Joint`, written as `Equal(x | y & z, x) → Equal(x | y, x)`: the
conditional `Pr(x | y & z) = Pr(x)` (independence of `x` from the pair) entails the
marginal conditional `Pr(x | y) = Pr(x)`.

The proof is a direct application of `IndepFun.comp`: independence of `x` from `(y, z)`
is preserved under post-composing the second argument with the measurable projection
`Prod.fst`, and `Prod.fst ∘ (y, z) = y`. No density / `PSpace` assumptions are needed —
independence is a σ-algebra property.
-/
@[main]
private lemma fst
  {Ω α β γ : Type*}
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β] [ReferenceMeasure γ]
  {𝕡 : Measure Ω}
  {x : Ω → α} {y : Ω → β} {z : Ω → γ}
-- given
  (h : x ⟂ᵢ[𝕡] (y, z)) :
-- imply
  x ⟂ᵢ[𝕡] y :=
-- proof
  h.comp measurable_id measurable_fst


/--
If a random variable `x` is independent of a joint random variable `(y, z)`, then it is
independent of the second component `z` (the `wrt = 1` case of the sympy lemma).
-/
@[main]
private lemma snd
  {Ω α β γ : Type*}
  [MeasurableSpace Ω]
  [ReferenceMeasure α] [ReferenceMeasure β] [ReferenceMeasure γ]
  {𝕡 : Measure Ω}
  {x : Ω → α} {y : Ω → β} {z : Ω → γ}
-- given
  (h : x ⟂ᵢ[𝕡] (y, z)) :
-- imply
  x ⟂ᵢ[𝕡] z :=
-- proof
  h.comp measurable_id measurable_snd


-- created on 2020-12-13
-- updated on 2026-09-14
