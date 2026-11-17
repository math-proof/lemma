import Lemma.Random.Map.eq.BindK.of.All_EqWithDensity
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Kernel


/-- `κ.comap f ∘ₘ μ = κ ∘ₘ (μ.map f)`. -/
private lemma comp_comap_eq_comp_map
  {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  (κ : Kernel β γ) [IsSFiniteKernel κ] (μ : Measure α) [SFinite μ]
  {f : α → β} (hf : Measurable f) :
  κ.comap f hf ∘ₘ μ = κ ∘ₘ (μ.map f) := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.bind_apply hs (Kernel.aemeasurable _),
    Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp_rw [Kernel.comap_apply]
  exact (lintegral_map (κ.measurable_coe hs) hf).symm

/--
Next-state law under the continuous-action trajectory model:
`law(s[t+1]) = T ∘ₘ law(s[t], a[t])`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ) :
-- imply
  (M.traj θ).map (s (t + 1)) =
    M.transK ∘ₘ (M.traj θ).map (fun ω ↦ (s t ω, a t ω)) := by
-- proof
  obtain rfl : s = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 :=
    funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₀ t) ω)).symm
  set s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜 := fun t ω ↦ (ω t).2.2
  set μ := (M.traj θ).map (fun ω ↦ ω t)
  have hK := Map.eq.BindK.of.All_EqWithDensity (M := M) θ t
  have hmap :
    (M.traj θ).map (s (t + 1)) =
      ((M.traj θ).map (fun ω ↦ ω (t + 1))).map (fun z ↦ z.2.1) := by
    rw [Measure.map_map measurable_snd.fst (measurable_pi_apply (t + 1))]; rfl
  have hsa :
    (M.traj θ).map (fun ω ↦ (s t ω, a t ω)) = μ.map (fun z ↦ z.2) := by
    rw [Measure.map_map (measurable_snd.fst.prodMk measurable_snd.snd)
      (measurable_pi_apply t)]
    rfl
  have hsk :
    (M.stageK θ).map (fun z : ℝ × 𝒮 × 𝒜 => z.2.1) =
      Kernel.deterministic (id : 𝒮 → 𝒮) measurable_id := by
    unfold Model.stageK
    rw [← Kernel.map_comp_right _ (by fun_prop) (by fun_prop)]
    show (Kernel.deterministic id measurable_id ×ₖ
        (M.kernel θ ⊗ₖ M.rewardK)).map Prod.fst = _
    rw [← Kernel.fst_eq]
    exact Kernel.fst_prod _ _
  rw [hmap, hK, Model.K, ← Measure.comp_assoc,
    Measure.map_comp _ _ (by fun_prop), hsk,
    Measure.deterministic_comp_eq_map, Measure.map_id, hsa,
    comp_comap_eq_comp_map]


-- created on 2026-10-20
-- updated on 2026-11-16
