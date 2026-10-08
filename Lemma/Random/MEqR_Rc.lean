import sympy.stats.policy_trajectory
import sympy.Basic
import Lemma.Random.Map.eq.StageK
import Lemma.Random.StageKSetOf1.eq.Zero
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random


/--
Almost surely the reward equals the clamped reward: `r[t] =ᵐ rc(ω[t])`, i.e. `r t ω = M.rc (ω t)` for a.e. trajectory `ω`.
-/
@[main]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [Fintype A]
  {M : Model Θ S A}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ) :
-- imply
  r t =ᵐ[M θ] fun ω ↦ M.rc (ω t) := by
-- proof
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁ t) ω)).symm
  have hs : MeasurableSet {z : ℝ × S × A | z.1 ∉ Set.Icc (-M.env.R) M.env.R} :=
    (measurableSet_Icc.compl).preimage measurable_fst
  have h : (M θ).map (fun ω => ω t) {z | z.1 ∉ Set.Icc (-M.env.R) M.env.R} = 0 := by
    rw [Map.eq.StageK h₁, Measure.bind_apply hs (Kernel.aemeasurable _)]
    exact (lintegral_congr (fun y => StageKSetOf1.eq.Zero (M := M) θ y)).trans lintegral_zero
  rw [Measure.map_apply (measurable_pi_apply t) hs] at h
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun ω hω => ?_) h
  simp only [Set.mem_ofPred_eq] at hω ⊢
  intro hI
  apply hω
  simp only [Model.rc]
  rw [min_eq_right hI.2, max_eq_right hI.1]


-- created on 2026-10-07
