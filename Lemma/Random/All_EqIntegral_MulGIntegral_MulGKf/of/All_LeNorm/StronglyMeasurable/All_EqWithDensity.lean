import Lemma.Random.Integral_Mul.eq.Integral_Mul_Integral.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
import Lemma.Random.Kf.eq.Integral.All_EqWithDensity
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Random Finset


/--
Iterated Markov property along histories: `𝔼[G(ω[..n]) * f(ω[n+j])] = 𝔼[G(ω[..n]) * Kf θ f j (ω[n])]`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [ReferenceMeasure A]
  {M : DensityModel Θ S A}
  {f : ℝ × S × A → ℝ}
  {C : ℝ}
-- given
  (hf : StronglyMeasurable f)
  (hC : ∀ z, ‖f z‖ ≤ C)
  (θ : Θ)
  (j : ℕ) :
-- imply
  ∀ n {G : (Π _ : Finset.Iic n, ℝ × S × A) → ℝ}, StronglyMeasurable G → ∀ {CG : ℝ}, (∀ h, ‖G h‖ ≤ CG) →
    ∫ ω, G (Preorder.frestrictLe n ω) * f (ω (n + j)) ∂(M θ) =
      ∫ ω, G (Preorder.frestrictLe n ω) * M.Kf θ f j (ω n) ∂(M θ) := by
-- proof
  induction j with
  | zero =>
    intro n G _ _ _
    rfl
  | succ j ih =>
    intro n G hG CG hCG
    have h₁ := ih (n + 1) (G := G ∘ Preorder.frestrictLe₂ (π := fun _ : ℕ => (ℝ × S × A)) (by omega : n ≤ n + 1))
      (hG.comp_measurable (Preorder.measurable_frestrictLe₂ _)) (CG := CG) (fun _ => hCG _)
    have e : n + (j + 1) = n + 1 + j := by omega
    rw [e]
    refine h₁.trans ?_
    have hKf := StronglyMeasurable_KfAndAll_LeNormKf.of.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M) hf hC θ j
    refine (Integral_Mul.eq.Integral_Mul_Integral.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable.All_EqWithDensity
      (M := M) (n := n) hG hCG hKf.1 hKf.2 θ).trans ?_
    simp_rw [← Kf.eq.Integral.All_EqWithDensity (M := M) θ j]


-- created on 2026-10-20
