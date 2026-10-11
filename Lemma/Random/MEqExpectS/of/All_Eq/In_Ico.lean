import Lemma.Random.CondIndep_Joint.of.All_EqJoint
import Lemma.Random.MEqExpectS.of.CondIndep.Integrable.MeasurableJoint.Measurable
import Lemma.Random.Integrable_G.of.In_Ico
open PolicyGradient Random


/--
Corollary of the Markov property `Random.CondIndep_Joint.of.All_EqJoint`: given `(s[t], a[t], s[t+1])` the
conditional expectation of the future discounted return `γ ** Stack[k](k) @ r[t+1:]` only depends on `s[t+1]`
(by `Random.MEqExpectS.of.CondIndep.Integrable.MeasurableJoint.Measurable`).
-/
@[path]
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
  𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t + 1:] | (s t, a t), s (t + 1)) =ᵐ[M θ]
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t + 1:] | s (t + 1)) := by
-- proof
  obtain rfl : r = fun t ω ↦ (ω t).1 :=
    funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 :=
    funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  apply MEqExpectS.of.CondIndep.Integrable.MeasurableJoint.Measurable
    (Measurable.tsum fun k ↦ (measurable_pi_apply k).const_mul _)
    ((Measurable.of_eval fun k ↦ (measurable_pi_apply (t + 1 + k)).fst).prodMk
      (((measurable_pi_apply t).snd.fst.prodMk (measurable_pi_apply t).snd.snd).prodMk
        (measurable_pi_apply (t + 1)).snd.fst))
    (Integrable_G.of.In_Ico (M := M) h₀ h₁ θ (t + 1))
    (CondIndep_Joint.of.All_EqJoint (fun t ↦ (h₁ t).symm))


-- created on 2026-10-10
