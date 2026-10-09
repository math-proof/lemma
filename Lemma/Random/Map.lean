import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Measure.MapComap_MapId.eq.Map.of.Measurable
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Measure Finset


/--
Joint law of two consecutive stages of the trajectory model `M`: `law(ω[t], ω[t+1]) = law(ω[t]) ⊗ₘ K θ`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
-- given
  (θ : Θ)
  (t : ℕ) :
-- imply
  (M θ).map (fun ω => (ω t, ω (t + 1))) = ((M θ).map (fun ω => ω t)) ⊗ₘ M.K θ := by
-- proof
  have h := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ ↦ ℝ × S × A) (μ₀ := M.μ₀ θ) (κ := M.step θ) (a := t)
  let e : (Π _ : Finset.Iic t, ℝ × S × A) → ℝ × S × A := fun h ↦ h ⟨t, mem_Iic.2 le_rfl⟩
  have he : Measurable e := measurable_pi_apply _
  have h₂ := congrArg (Measure.map (Prod.map e id)) h
  rw [Measure.map_map (he.prodMap measurable_id) (by fun_prop)] at h₂
  have h₃ : M.step θ t = (M.K θ).comap e he := rfl
  rw [h₃, MapComap_MapId.eq.Map.of.Measurable he, Measure.map_map he (by fun_prop)] at h₂
  exact h₂.symm


-- created on 2026-10-07
