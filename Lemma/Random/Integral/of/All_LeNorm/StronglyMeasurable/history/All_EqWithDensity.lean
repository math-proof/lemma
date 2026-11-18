import Def.Dynamics.PolicyTrajectory.ContinuousAction
import Class.Dynamics.MarkovDecisionProcess
import Instance.Dynamics.PolicyTrajectory
import Initialize.Tactic.Attr.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Finset


/--
One-step Markov property along histories of the continuous-action trajectory model `M`:
`𝔼[φ(ω[..n], ω[n+1])] = ∫ h, ∫ z, φ (h, z) ∂(K θ h[n]) ∂law(ω[..n])`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {n : ℕ}
  {φ : (Π _ : Finset.Iic n, ℝ × 𝒮 × 𝒜) × (ℝ × 𝒮 × 𝒜) → ℝ}
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
  let μ₀ : Measure (ℝ × 𝒮 × 𝒜) := M.stageK θ ∘ₘ (M.init : Measure _)
  have h := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ ↦ ℝ × 𝒮 × 𝒜) (μ₀ := μ₀) (κ := M.step θ) (a := n)
  have e : ∫ ω, φ (Preorder.frestrictLe n ω, ω (n + 1)) ∂(M θ) =
      ∫ p, φ p ∂((M θ).map (fun x ↦ (Preorder.frestrictLe n x, x (n + 1)))) := by
    rw [integral_map (by fun_prop) hφ.aestronglyMeasurable]
  rw [e]
  unfold Model.traj
  rw [← h, Measure.integral_compProd]
  · rfl
  · apply Integrable.of_bound hφ.aestronglyMeasurable C (Filter.Eventually.of_forall hC)


-- created on 2026-10-20
-- updated on 2026-11-18