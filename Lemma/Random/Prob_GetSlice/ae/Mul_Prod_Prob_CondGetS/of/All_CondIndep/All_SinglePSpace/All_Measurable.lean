import Lemma.Random.Prob_GetSlice.ae.Prob.of.All_SinglePSpace_GetSlice.All_MeasurableGet
import Lemma.Random.Prob_GetSlice.ae.MulProbS.of.All_SinglePSpace.All_Measurable
import Lemma.Random.Prob_CondGet__GetSlice.ae.Prob_CondGet__Get.of.All_Cond_Get.All_SinglePSpace_GetSlice.All_MeasurableGet
import Lemma.Random.Prob_GetSlice.ae.Prod_Prob_Cond.of.All_SinglePSpace.All_Measurable
import Lemma.Random.All_SinglePSpace_Joint.of.All_SinglePSpace_GetSlice
import Lemma.Random.All_SinglePSpace_JointGet_Add_1_Get.of.All_SinglePSpace_GetSlice
import Lemma.Random.All_MeasurableGet.is.All_MeasurableGetSlice
import Notation.Probability.JointRv
import Notation.Fun
import Syntax.Probability.Probability
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Independence.Conditional
open MeasureTheory ProbabilityTheory Random Fun
open scoped ProbabilityTheory


/--
Markov factorization of a process prefix. If the process satisfies the
first-order Markov property `s[t + 1] ⟂ᵢ[π] s[:t] | s[t]` at every time, then
the chain rule
[prefix density as a product of conditionals on the full past](?module=Random.Prob_GetSlice.ae.Prod_Prob_Cond.of.All_SinglePSpace.All_Measurable)
collapses to conditionals on the previous state only:

  \(\mathbb{P}_{\pi}(s[:n+1]) = \mathbb{P}_{\pi}(s[0]) \prod_{k<n} \mathbb{P}_{\pi}(s[k+1] \mid s[k])\).

The identity holds almost surely with respect to \(\pi\), as a product of
random-argument densities.
-/
@[path]
private lemma main
  [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [ReferenceMeasure 𝒮] [StandardBorelSpace 𝒮] [Nonempty 𝒮]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {s : ℕ ⇀ Ω → 𝒮}
-- given
  (hs : ∀ k, Measurable s[k])
  (hP : ∀ n, SinglePSpace π (s[:n] : Ω → Fin n → 𝒮))
  (hmarkov : ∀ (t : ℕ), s[t + 1] ⟂ᵢ[π] s[:t] | s[t])
  (n : ℕ) :
-- imply
  have : ∀ k : ℕ, Measurable s[:k] :=
    All_MeasurableGetSlice.of.All_MeasurableGet hs
  have : SinglePSpace π s[:n + 1] := hP (n + 1)
  have : SinglePSpace π s[0] :=
    SinglePSpace.of.SinglePSpace.fst (All_SinglePSpace_Joint.of.All_SinglePSpace_GetSlice hP 0)
  have : ∀ k, SinglePSpace π (s[k + 1], s[k]) := All_SinglePSpace_JointGet_Add_1_Get.of.All_SinglePSpace_GetSlice hP
  ℙ[π](s[:n + 1]) =ᵐ[π]
    ℙ[π](s[0]) * ∏ k ∈ Finset.range n, ℙ[π](s[k + 1] | s[k]) := by
-- proof
  intro _ _ _ _
  induction n with
  | zero =>
    have h1 :=
      Prob_GetSlice.ae.Prob.of.All_SinglePSpace_GetSlice.All_MeasurableGet hs hP
    filter_upwards [h1] with ω h
    simp [Pi.mul_apply, mul_one]
    convert h
  | succ m ih =>
    have hstep :=
      Prob_GetSlice.ae.MulProbS.of.All_SinglePSpace.All_Measurable hs hP m.succ
    have hmark :=
      Prob_CondGet__GetSlice.ae.Prob_CondGet__Get.of.All_Cond_Get.All_SinglePSpace_GetSlice.All_MeasurableGet hs hP hmarkov m
    have ih' := ih
    filter_upwards [hstep, hmark, ih'] with ω h₁ h₂ h₃
    simp only [Finset.prod_range_succ, Pi.mul_apply] at h₁ h₂ h₃ ⊢
    push_cast at h₁ h₂ h₃ ⊢
    rw [h₁, h₂, h₃]
    ac_rfl


-- created on 2026-11-18
