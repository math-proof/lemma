import sympy.core.power
import sympy.vector.Basic
import Lemma.Random.CondIndep_Joint.of.All_EqJoint
import Lemma.Random.MEqExpect.of.CondIndep.Integrable.Measurable.Measurable.Measurable.Measurable
import Lemma.Random.Integrable_G.of.In_Ico
open MeasureTheory ProbabilityTheory PolicyGradient Random


/--
Corollary of the Markov property `Random.CondIndep_Joint.of.All_EqJoint`: given `(s[t], a[t], s[t+1])` the
conditional expectation of the future discounted return `γ ** Stack[k](k) @ r[t+1:]` only depends on `s[t+1]`
(by `Random.MEqExpect.of.CondIndep.Integrable.Measurable.Measurable.Measurable.Measurable`).
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
  {θ : Θ}
  {γ : ℝ}
  {t : ℕ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t)) :
-- imply
  (M θ)[(fun ω ↦ (γ ^ (id : ℕ → ℕ)) @ (r · ω)[t + 1:]) | MeasurableSpace.comap (fun ω ↦ ((s t ω, a t ω), s (t + 1) ω)) inferInstance] =ᵐ[M θ]
    (M θ)[(fun ω ↦ (γ ^ (id : ℕ → ℕ)) @ (r · ω)[t + 1:]) | MeasurableSpace.comap (s (t + 1)) inferInstance] := by
-- proof
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  apply MEqExpect.of.CondIndep.Integrable.Measurable.Measurable.Measurable.Measurable
    (measurable_pi_lambda _ fun k ↦ (measurable_pi_apply (t + 1 + k)).fst)
    ((measurable_pi_apply t).snd.fst.prodMk (measurable_pi_apply t).snd.snd)
    (measurable_pi_apply (t + 1)).snd.fst
    (Measurable.tsum fun k ↦ (measurable_pi_apply k).const_mul _)
    (Integrable_G.of.In_Ico (M := M) θ h₀ (t + 1) h₁) (CondIndep_Joint.of.All_EqJoint (fun t ↦ (h₁ t).symm))


-- created on 2026-10-06
-- updated on 2026-10-08
