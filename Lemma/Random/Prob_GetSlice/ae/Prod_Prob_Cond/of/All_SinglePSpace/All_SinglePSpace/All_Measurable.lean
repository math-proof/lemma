import Lemma.Random.SinglePSpace.of.SinglePSpace
import Lemma.Random.Prob_Cond_Joint.ae.Prob_Cond.of.SinglePSpace
import Lemma.Random.Prob_Cond.ae.Prob.of.SinglePSpace.SinglePSpace
import Lemma.Random.Prob_Cond.ae.Prod_Prob_Cond_Joint.of.Measurable.All_Measurable
import Lemma.Random.All_MeasurableGet.is.All_MeasurableGetSlice
import Lemma.Random.All_SinglePSpace_JointGet__GetSlice.of.All_SinglePSpace_GetSlice
import Syntax.Probability.Probability
import Notation.Fun
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Measure.Prod
open MeasureTheory ProbabilityTheory Random Fun


/--
Chain rule for a process prefix:

  \(\mathbb{P}_{\pi}(s[:n]) = \prod_{k<n} \mathbb{P}_{\pi}(s[k] \mid s[:k])\).

The identity holds almost surely with respect to \(\pi\), as a ratio of densities
against the product reference measure on prefixes. It is the special case of
[the conditional chain rule](?module=Random.Prob_Cond.ae.Prod_Prob_Cond_Joint.of.Measurable.All_Measurable)
with a deterministic auxiliary variable.
-/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure 𝒮]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {s : ℕ ⇀ Ω → 𝒮}
-- given
  (hs : ∀ k, Measurable s[k])
  (hP : ∀ n, SinglePSpace π (s[:n] : Ω → Fin n → 𝒮))
  (n : ℕ) :
-- imply
  have : ∀ k : ℕ, Measurable s[:k] :=
    All_MeasurableGetSlice.of.All_MeasurableGet hs
  have : ∀ k, SinglePSpace π (s[k], s[:k]) :=
    All_SinglePSpace_JointGet__GetSlice.of.All_SinglePSpace_GetSlice hP
  ℙ[π](s[:n]) =ᵐ[π] ∏ k ∈ Finset.range n, ℙ[π](s[k] | s[:k]) := by
-- proof
  have hPstep : ∀ k, SinglePSpace π (s[k], s[:k]) :=
    All_SinglePSpace_JointGet__GetSlice.of.All_SinglePSpace_GetSlice hP
  let Z : Ω → Fin 0 → 𝒮 := fun _ => Fin.elim0
  have hZ : Measurable Z := measurable_const
  have hPZ' :
    ∀ k : ℕ, SinglePSpace π (fun ω => (s[:k] : Ω → Fin k → 𝒮) ω, Z) :=
    fun k => SinglePSpace.of.SinglePSpace (hP k)
  have hPstep' :
    ∀ k : ℕ,
      SinglePSpace π
        (s[k], fun ω => (s[:k] : Ω → Fin k → 𝒮) ω, Z) :=
    fun k =>
      PSpace_Joint_Joint.of.PSpace_JointJoint
        (SinglePSpace.of.SinglePSpace (hPstep k))
  have hutil :
    ℙ[π](s[:n] | Z) =ᵐ[π]
      ∏ k ∈ Finset.range n, ℙ[π](s[k] | s[:k], Z) :=
    @Prob_Cond.ae.Prod_Prob_Cond_Joint.of.Measurable.All_Measurable
      Ω 𝒮 (Fin 0 → 𝒮) _ _ ReferenceMeasure.piFin π _ s Z hs hZ hPZ' n
  have hleft : ℙ[π](s[:n] | Z) =ᵐ[π] ℙ[π](s[:n]) :=
    Prob_Cond.ae.Prob.of.SinglePSpace.SinglePSpace (hP n) (hPZ' n)
  have hstep (k : ℕ) :
    ℙ[π](s[k] | s[:k], Z) =ᵐ[π] ℙ[π](s[k] | s[:k]) :=
    Prob_Cond_Joint.ae.Prob_Cond.of.SinglePSpace (hPstep' k)
  have hprod (n : ℕ) :
    (∏ k ∈ Finset.range n, ℙ[π](s[k] | s[:k], Z)) =ᵐ[π]
      (∏ k ∈ Finset.range n, ℙ[π](s[k] | s[:k])) := by
    induction n with
    | zero =>
      simp
    | succ m ih =>
      filter_upwards [ih, hstep m] with ω h₁ h₂
      simp only [Finset.prod_range_succ, Pi.mul_apply] at h₁ h₂ ⊢
      rw [h₁, h₂]
  filter_upwards [hutil, hleft, hprod n] with ω h₁ h₂ h₃
  exact h₂.symm.trans (h₁.trans h₃)


-- created on 2023-04-08
-- updated on 2026-11-18
