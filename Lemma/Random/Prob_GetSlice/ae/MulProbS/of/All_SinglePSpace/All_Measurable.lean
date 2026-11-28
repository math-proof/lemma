import Lemma.Random.Prob_GetSlice.ae.Prod_Prob_Cond.of.All_SinglePSpace.All_Measurable
import Lemma.Random.All_MeasurableGet.is.All_MeasurableGetSlice
import Lemma.Random.All_SinglePSpace_Joint.of.All_SinglePSpace_GetSlice
import Notation.Probability.JointRv
import Notation.Fun
import Syntax.Probability.Probability
import Mathlib.MeasureTheory.Measure.Prod
import Instance.Data.Nat.Fun
open MeasureTheory ProbabilityTheory Random Fun
open scoped ProbabilityTheory


/--
One-step chain rule for a prefix density:

  \(\mathbb{P}_{\pi}(s[:n+1]) = \mathbb{P}_{\pi}(s[n] \mid s[:n]) \cdot \mathbb{P}_{\pi}(s[:n])\).
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure 𝒮]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {s : ℕ → Ω → 𝒮}
-- given
  (hs : ∀ k, Measurable s[k])
  (hP : ∀ n, SinglePSpace π (s[:n] : Ω → Fin n → 𝒮))
  (n : ℕ) :
-- imply
  have : ∀ k : ℕ, Measurable s[:k] :=
    All_MeasurableGetSlice.of.All_MeasurableGet hs
  have : SinglePSpace π (s[:n.succ] : Ω → Fin n.succ → 𝒮) := hP n.succ
  have : SinglePSpace π (s[:n] : Ω → Fin n → 𝒮) := hP n
  have : SinglePSpace π (s[n], fun ω => s[:n] ω) := All_SinglePSpace_Joint.of.All_SinglePSpace_GetSlice hP n
  ℙ[π](s[:n.succ]) =ᵐ[π] ℙ[π](s[n] | s[:n]) * ℙ[π](s[:n]) := by
-- proof
  intro _ _ _ _
  have hsucc :=
    Prob_GetSlice.ae.Prod_Prob_Cond.of.All_SinglePSpace.All_Measurable hs hP n.succ
  have hpref :=
    Prob_GetSlice.ae.Prod_Prob_Cond.of.All_SinglePSpace.All_Measurable hs hP n
  filter_upwards [hsucc, hpref] with ω h₁ h₂
  rw [h₁]
  simp only [Pi.mul_apply]
  rw [h₂, Finset.prod_apply, Finset.prod_apply, Nat.Iio_eq_range, Nat.Iio_eq_range,
    Finset.prod_range_succ, mul_comm]


-- created on 2026-11-19
-- updated on 2026-11-28
