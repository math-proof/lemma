import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.Integral.eq.Integral_Integral.of.All_LeNorm.StronglyMeasurable.history
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Finset


/--
Markov property along histories: `𝔼[G(ω[..n]) * g(ω[n+1])] = 𝔼[G(ω[..n]) * ∫ z, g z ∂(K θ ω[n])]`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {n : ℕ}
  {G : (Π _ : Finset.Iic n, ℝ × S × A) → ℝ}
  {CG : ℝ}
  {g : ℝ × S × A → ℝ}
  {C : ℝ}
-- given
  (hG : StronglyMeasurable G)
  (hCG : ∀ h, ‖G h‖ ≤ CG)
  (hg : StronglyMeasurable g)
  (hC : ∀ z, ‖g z‖ ≤ C)
  (θ : Θ) :
-- imply
  ∫ ω, G (Preorder.frestrictLe n ω) * g (ω (n + 1)) ∂(M θ) =
    ∫ ω, G (Preorder.frestrictLe n ω) * ∫ z, g z ∂(M.K θ (ω n)) ∂(M θ) := by
-- proof
  rw [Integral.eq.Integral_Integral.of.All_LeNorm.StronglyMeasurable.history (M := M) ((hG.comp_measurable measurable_fst).mul (hg.comp_measurable measurable_snd)) (n := n) (φ := fun p => G p.1 * g p.2)
    (fun p => by
      rw [norm_mul]
      exact mul_le_mul (hCG _) (hC _) (norm_nonneg _) ((norm_nonneg _).trans (hCG p.1))) (C := CG * C)
    θ]
  simp_rw [integral_const_mul]
  have hm : StronglyMeasurable (fun h : (Π _ : Finset.Iic n, ℝ × S × A) =>
      G h * ∫ z, g z ∂(M.K θ (h ⟨n, mem_Iic.2 le_rfl⟩))) := by
    refine hG.mul ?_
    exact (hg.comp_measurable measurable_snd).integral_kernel_prod_right' (κ := M.step θ n)
  rw [integral_map (by fun_prop) hm.aestronglyMeasurable]
  rfl


-- created on 2026-10-07
