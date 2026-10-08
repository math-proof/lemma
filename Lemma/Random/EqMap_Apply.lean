import sympy.stats.policy_trajectory
import sympy.Basic
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Finset


/--
The initial stage of the trajectory model `M` is distributed as `μ₀ θ`: `ω[0] ∼ μ₀ θ`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
-- given
  (θ : Θ) :
-- imply
  (M θ).map (fun ω => ω 0) = M.μ₀ θ := by
-- proof
  unfold Model.traj Kernel.trajMeasure
  rw [Measure.map_comp _ _ (measurable_pi_apply 0)]
  have h₁ : (Kernel.traj (X := fun _ ↦ ℝ × S × A) (M.step θ) 0).map (fun ω => ω 0) =
      ((Kernel.traj (X := fun _ ↦ ℝ × S × A) (M.step θ) 0).map (Preorder.frestrictLe 0)).map
        (fun h => h ⟨0, mem_Iic.2 le_rfl⟩) := by
    rw [← Kernel.map_comp_right _ (by fun_prop) (by fun_prop)]
    rfl
  rw [h₁, Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Kernel.id_map (by fun_prop),
    Measure.deterministic_comp_eq_map, Measure.map_map (by fun_prop) (by fun_prop)]
  have h₂ : ((fun h : (Π _ : Finset.Iic 0, ℝ × S × A) => h ⟨0, mem_Iic.2 le_rfl⟩) ∘
      ⇑(MeasurableEquiv.piUnique (fun i : Finset.Iic 0 => (fun _ => (ℝ × S × A)) i)).symm) = id := by
    funext x; rfl
  rw [h₂, Measure.map_id]


-- created on 2026-10-07
