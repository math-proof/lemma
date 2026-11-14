import Instance.Probability.Process.HiddenMarkovSequence
import Mathlib.Probability.Independence.Conditional
import Notation.Fun
open MeasureTheory ProbabilityTheory Fun
open scoped ProbabilityTheory


/--
First-order Markov processes forget the distant past down to the initial state:
if `s[t + 1]` is conditionally independent of the prefix `s[:t]` given `s[t]` at
every time and `0 < k`, then `s[k + 1]` is conditionally independent of `s[0]`
given `s[k]`.
-/
@[path]
private lemma main
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [MeasurableSpace 𝒮]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {s : ℕ ⇀ Ω → 𝒮}
  {k : ℕ}
-- given
  (hs : ∀ t, Measurable s[t])
  (hmarkov : ∀ t, s[t + 1] ⟂ᵢ[s t, hs t; π] s[:t])
  (hk : 0 < k) :
-- imply
  s[k + 1] ⟂ᵢ[s k, hs k; π] s[0] := by
-- proof
  have hCI :=
    (hmarkov k).comp measurable_id (measurable_pi_apply (⟨0, hk⟩ : Fin k))
  have hid : (id ∘ s[k + 1]) = s[k + 1] := funext fun _ ↦ rfl
  have hs0 : ((fun p : Fin k → 𝒮 ↦ p ⟨0, hk⟩) ∘ s[:k]) = s[0] := by
    funext ω
    simp [Function.comp, Fun.getSlice, Function.getSlice, FunSlice.slice]
  rwa [hid, hs0] at hCI


-- created on 2026-11-13
