import sympy.stats.policy_trajectory
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Finset


/--
One-step Markov property along histories of the trajectory model `M`:
`𝔼[φ(ω[..n], ω[n+1])] = ∫ h, ∫ z, φ (h, z) ∂(K θ h[n]) ∂law(ω[..n])`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {n : ℕ}
  {φ : (Π _ : Finset.Iic n, ℝ × S × A) × (ℝ × S × A) → ℝ}
  {C : ℝ}
-- given
  (hφ : StronglyMeasurable φ)
  (hC : ∀ p, ‖φ p‖ ≤ C)
  (θ : Θ) :
-- imply
  ∫ ω, φ (Preorder.frestrictLe n ω, ω (n + 1)) ∂(M θ) =
    ∫ h, ∫ z, φ (h, z) ∂(M.K θ (h ⟨n, mem_Iic.2 le_rfl⟩))
      ∂((M θ).map (Preorder.frestrictLe n)) := by
-- proof
  have h := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ ↦ ℝ × S × A) (μ₀ := M.μ₀ θ) (κ := M.step θ) (a := n)
  have e : ∫ ω, φ (Preorder.frestrictLe n ω, ω (n + 1)) ∂(M θ) =
      ∫ p, φ p ∂((M θ).map (fun x ↦ (Preorder.frestrictLe n x, x (n + 1)))) := by
    rw [integral_map (by fun_prop) hφ.aestronglyMeasurable]
  rw [e]
  unfold Model.traj
  rw [← h, Measure.integral_compProd]
  · rfl
  · exact Integrable.of_bound hφ.aestronglyMeasurable C (Filter.Eventually.of_forall hC)


-- created on 2026-10-07
