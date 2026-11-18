import Lemma.Random.Map.eq.CompProd.of.All_EqWithDensity
import Lemma.Random.Map.eq.BindStageK.of.All_Eq_Joint.All_EqWithDensity
import Def.Probability.Process.HiddenMarkovSequence.Part2
import Notation.Probability.JointRv
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Random Measure Finset
open scoped ProbabilityTheory


/--
If a kernel depends on the source only through `f`, adjoining any measurable `g`
preserves the factorization.
-/
private lemma map_compProd_comap_prod
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
  {ν : Measure α} [SFinite ν]
  {κ : Kernel β γ} [IsSFiniteKernel κ]
  {f : α → β} {g : α → δ}
-- given
  (hf : Measurable f) (hg : Measurable g) :
-- imply
  (ν ⊗ₘ κ.comap f hf).map (Prod.map (fun a => (f a, g a)) id) =
    ν.map (fun a => (f a, g a)) ⊗ₘ κ.comap Prod.fst (by fun_prop) := by
-- proof
  have hφ : Measurable fun a => (f a, g a) := hf.prodMk hg
  ext s hs
  rw [Measure.map_apply (hφ.prodMap measurable_id) hs, Measure.compProd_apply,
    Measure.compProd_apply hs]
  ·
    rw [lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hφ]
    rfl
  ·
    exact hφ.prodMap measurable_id hs

/--
The state component of a stage drawn from `stageK θ` is the given state.
-/
private lemma map_stageK_state
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
-- given
  (θ : Θ) :
-- imply
  (M.stageK θ).map (fun z : ℝ × 𝒮 × 𝒜 => z.2.1) =
    Kernel.deterministic (id : 𝒮 → 𝒮) measurable_id := by
-- proof
  unfold Model.stageK
  rw [← Kernel.map_comp_right _ (by fun_prop) (by fun_prop)]
  show (Kernel.deterministic id measurable_id ×ₖ (M.kernel θ ⊗ₖ M.rewardK)).map Prod.fst = _
  rw [← Kernel.fst_eq]
  exact Kernel.fst_prod _ _

/--
The next state of a stage is drawn from the transition kernel of the current
state-action pair.
-/
private lemma map_K_state
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
-- given
  (θ : Θ) :
-- imply
  (M.K θ).map (fun z : ℝ × 𝒮 × 𝒜 => z.2.1) =
    M.transK.comap (fun z => z.2) (by fun_prop) := by
-- proof
  unfold Model.K
  rw [Kernel.map_comp, map_stageK_state (M := M) θ, Kernel.deterministic_comp_eq_map measurable_id,
    Kernel.map_id]

/--
A draw from `stageK θ` is supported on the given state, so pairing the stage
with its state recovers `Kernel.id ×ₖ stageK θ`.
-/
private lemma map_stageK_prod
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
-- given
  (θ : Θ) :
-- imply
  (M.stageK θ).map (fun z : ℝ × 𝒮 × 𝒜 => (z.2.1, z)) =
    Kernel.id ×ₖ M.stageK θ := by
-- proof
  unfold Model.stageK
  rw [← Kernel.map_comp_right _ (by fun_prop) (by fun_prop)]
  refine Kernel.ext fun y => ?_
  rw [Kernel.map_apply _ (by fun_prop) y]
  have hre :
    ((fun z : ℝ × 𝒮 × 𝒜 => (z.2.1, z)) ∘ fun z : 𝒮 × 𝒜 × ℝ => (z.2.2, z.1, z.2.1)) =
      fun z => (z.1, (z.2.2, z.1, z.2.1)) :=
    rfl
  rw [hre, Kernel.prod_apply, Kernel.deterministic_apply]
  simp only [id]
  rw [Kernel.prod_apply, Kernel.id_apply, Kernel.map_apply _ (by fun_prop) y,
    Kernel.prod_apply, Kernel.deterministic_apply]
  simp only [id]
  rw [Measure.dirac_prod, Measure.map_map (by fun_prop) (by fun_prop), Measure.dirac_prod,
    Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/--
The one-step kernel from a state: sample a stage from `stageK`, the next state
from `trans`, and return the current action, reward, and next state.
-/
private lemma map_compProd_stageK_K
  [MeasurableSpace 𝒮] [StandardBorelSpace 𝒮]
  [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {ν : Measure 𝒮} [SFinite ν]
-- given
  (θ : Θ) :
-- imply
  ((M.stageK θ ∘ₘ ν) ⊗ₘ M.K θ).map
      (fun p : (ℝ × 𝒮 × 𝒜) × (ℝ × 𝒮 × 𝒜) => (p.1.2.1, (p.1.2.2, p.1.1, p.2.2.1))) =
    ν ⊗ₘ
      ((M.stageK θ ⊗ₖ
          M.transK.comap (fun p : 𝒮 × (ℝ × 𝒮 × 𝒜) => p.2.2) (by fun_prop)).map
        (fun p : (ℝ × 𝒮 × 𝒜) × 𝒮 => (p.1.2.2, p.1.1, p.2))) := by
-- proof
  have hid_map :
    (fun p : (ℝ × 𝒮 × 𝒜) × (ℝ × 𝒮 × 𝒜) => (p.1, p.2.2.1)) =
      Prod.map id (fun z : ℝ × 𝒮 × 𝒜 => z.2.1) :=
    rfl
  have hnext :
    ((M.stageK θ ∘ₘ ν) ⊗ₘ M.K θ).map
        (fun p : (ℝ × 𝒮 × 𝒜) × (ℝ × 𝒮 × 𝒜) => (p.1, p.2.2.1)) =
      (M.stageK θ ∘ₘ ν) ⊗ₘ M.transK.comap (fun z : ℝ × 𝒮 × 𝒜 => z.2) (by fun_prop) := by
    rw [hid_map, ← Measure.compProd_map (by fun_prop : Measurable (fun z : ℝ × 𝒮 × 𝒜 => z.2.1)),
      map_K_state (M := M) θ]
  have hpush :
    ((M.stageK θ ∘ₘ ν) ⊗ₘ M.K θ).map
        (fun p : (ℝ × 𝒮 × 𝒜) × (ℝ × 𝒮 × 𝒜) => (p.1.2.1, (p.1.2.2, p.1.1, p.2.2.1))) =
      ((M.stageK θ ∘ₘ ν) ⊗ₘ M.transK.comap (fun z : ℝ × 𝒮 × 𝒜 => z.2) (by fun_prop)).map
        (fun p : (ℝ × 𝒮 × 𝒜) × 𝒮 => (p.1.2.1, (p.1.2.2, p.1.1, p.2))) := by
    have h :=
      congrArg
        (Measure.map (fun p : (ℝ × 𝒮 × 𝒜) × 𝒮 => (p.1.2.1, (p.1.2.2, p.1.1, p.2))))
        hnext
    rw [Measure.map_map (by fun_prop) (by fun_prop)] at h
    have hfun :
      (fun p : (ℝ × 𝒮 × 𝒜) × (ℝ × 𝒮 × 𝒜) => (p.1.2.1, (p.1.2.2, p.1.1, p.2.2.1))) =
        (fun p : (ℝ × 𝒮 × 𝒜) × 𝒮 => (p.1.2.1, (p.1.2.2, p.1.1, p.2))) ∘
          fun p => (p.1, p.2.2.1) :=
      rfl
    rw [hfun]
    exact h
  have hkernel :
    (Kernel.id ×ₖ M.transK.comap (fun z : ℝ × 𝒮 × 𝒜 => z.2) (by fun_prop)) ∘ₖ M.stageK θ =
      M.stageK θ ⊗ₖ
        M.transK.comap (fun p : 𝒮 × (ℝ × 𝒮 × 𝒜) => p.2.2) (by fun_prop) := by
    refine Kernel.ext fun y => ?_
    have hL :
      ((Kernel.id ×ₖ M.transK.comap (fun z : ℝ × 𝒮 × 𝒜 => z.2) (by fun_prop)) ∘ₖ M.stageK θ) y =
        (M.stageK θ y) ⊗ₘ M.transK.comap (fun z : ℝ × 𝒮 × 𝒜 => z.2) (by fun_prop) := by
      rw [Kernel.comp_apply, ← Measure.compProd_eq_comp_prod]
    have hR :
      (M.stageK θ ⊗ₖ
          M.transK.comap (fun p : 𝒮 × (ℝ × 𝒮 × 𝒜) => p.2.2) (by fun_prop)) y =
        (M.stageK θ y) ⊗ₘ
          (M.transK.comap (fun p : 𝒮 × (ℝ × 𝒮 × 𝒜) => p.2.2) (by fun_prop)).comap
            (fun z => (y, z)) (by fun_prop) := by
      -- Evaluate both sides on measurable sets.
      ext s hs
      rw [Kernel.compProd_apply hs, Measure.compProd_apply hs]
      rfl
    refine hL.trans ?_
    refine Eq.trans ?_ hR.symm
    -- `transK.comap (·.2) z = transK.comap (fun p => p.2.2) (y, z)`
    rfl
  have hcomp :
    (M.stageK θ ∘ₘ ν) ⊗ₘ M.transK.comap (fun z : ℝ × 𝒮 × 𝒜 => z.2) (by fun_prop) =
      (M.stageK θ ⊗ₖ
          M.transK.comap (fun p : 𝒮 × (ℝ × 𝒮 × 𝒜) => p.2.2) (by fun_prop)) ∘ₘ ν := by
    rw [Measure.compProd_eq_comp_prod, Measure.comp_assoc, hkernel]
  rw [hpush, hcomp, Measure.map_comp _ _ (by fun_prop)]
  have hdirac :
    (M.stageK θ ⊗ₖ
          M.transK.comap (fun p : 𝒮 × (ℝ × 𝒮 × 𝒜) => p.2.2) (by fun_prop)).map
        (fun p : (ℝ × 𝒮 × 𝒜) × 𝒮 => (p.1.2.1, (p.1.2.2, p.1.1, p.2))) =
      Kernel.id ×ₖ
        ((M.stageK θ ⊗ₖ
            M.transK.comap (fun p : 𝒮 × (ℝ × 𝒮 × 𝒜) => p.2.2) (by fun_prop)).map
          (fun p : (ℝ × 𝒮 × 𝒜) × 𝒮 => (p.1.2.2, p.1.1, p.2))) := by
    refine Kernel.ext fun y => ?_
    rw [Kernel.map_apply _ (by fun_prop) y, Kernel.prod_apply, Kernel.id_apply,
      Kernel.map_apply _ (by fun_prop) y]
    have hfst :
      ((M.stageK θ ⊗ₖ
            M.transK.comap (fun p : 𝒮 × (ℝ × 𝒮 × 𝒜) => p.2.2) (by fun_prop)) y).map Prod.fst =
        M.stageK θ y := by
      rw [← Kernel.fst_apply, Kernel.fst_compProd]
    have hz :
      (M.stageK θ y).map (fun z : ℝ × 𝒮 × 𝒜 => z.2.1) = Measure.dirac y := by
      have h := map_stageK_state (M := M) θ
      rw [← Kernel.map_apply _ (by fun_prop) y, h, Kernel.deterministic_apply]
      rfl
    have hstate :
      ((M.stageK θ ⊗ₖ
            M.transK.comap (fun p : 𝒮 × (ℝ × 𝒮 × 𝒜) => p.2.2) (by fun_prop)) y).map
          (fun p : (ℝ × 𝒮 × 𝒜) × 𝒮 => p.1.2.1) =
        Measure.dirac y := by
      have h := congrArg (Measure.map (fun z : ℝ × 𝒮 × 𝒜 => z.2.1)) hfst
      rw [Measure.map_map (by fun_prop) measurable_fst] at h
      exact h.trans hz
    have hmeas : MeasurableSet ({y} : Set 𝒮) := measurableSet_singleton y
    let μy :=
      (M.stageK θ ⊗ₖ
        M.transK.comap (fun p : 𝒮 × (ℝ × 𝒮 × 𝒜) => p.2.2) (by fun_prop)) y
    have hone : μy ((fun p : (ℝ × 𝒮 × 𝒜) × 𝒮 => p.1.2.1) ⁻¹' {y}) = 1 := by
      have h :=
        Measure.map_apply (μ := μy)
          (by fun_prop : Measurable (fun p : (ℝ × 𝒮 × 𝒜) × 𝒮 => p.1.2.1)) hmeas
      rw [hstate, Measure.dirac_apply' _ hmeas] at h
      simpa using h.symm
    have hae : (fun p : (ℝ × 𝒮 × 𝒜) × 𝒮 => p.1.2.1) =ᵐ[μy] fun _ => y := by
      have : IsProbabilityMeasure μy := inferInstance
      change ∀ᵐ p ∂μy, p.1.2.1 = y
      rw [ae_iff]
      change μy ((fun p : (ℝ × 𝒮 × 𝒜) × 𝒮 => p.1.2.1) ⁻¹' {y})ᶜ = 0
      rw [prob_compl_eq_zero_iff (hmeas.preimage (by fun_prop))]
      exact hone
    have hae' :
      (fun p : (ℝ × 𝒮 × 𝒜) × 𝒮 => (p.1.2.1, (p.1.2.2, p.1.1, p.2))) =ᵐ[μy]
        fun p => (y, (p.1.2.2, p.1.1, p.2)) :=
      hae.mono fun p hp => by
        refine congrArg (fun s : 𝒮 => (s, (p.1.2.2, p.1.1, p.2))) ?_
        exact hp
    rw [Measure.map_congr hae', Measure.dirac_prod,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [hdirac, ← Measure.compProd_eq_comp_prod]


/--
Pairing the next stage with its state: `(K θ).map (fun z => (z.2.1, z))`
samples the next state from `trans` and the next stage from `stageK`.
-/
private lemma map_K_prod
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
-- given
  (θ : Θ) :
-- imply
  (M.K θ).map (fun z : ℝ × 𝒮 × 𝒜 => (z.2.1, z)) =
    M.transK.comap (fun z => z.2) (by fun_prop) ⊗ₖ
      (M.stageK θ).comap Prod.snd (by fun_prop) := by
-- proof
  unfold Model.K
  rw [Kernel.map_comp, map_stageK_prod (M := M) θ]
  refine Kernel.ext fun w => ?_
  have hL :
    ((Kernel.id ×ₖ M.stageK θ) ∘ₖ M.transK.comap (fun z => z.2) (by fun_prop)) w =
      (M.transK.comap (fun z => z.2) (by fun_prop) w) ⊗ₘ M.stageK θ := by
    rw [Kernel.comp_apply, ← Measure.compProd_eq_comp_prod]
  refine hL.trans ?_
  ext s hs
  rw [Measure.compProd_apply hs, Kernel.compProd_apply hs]
  rfl

/--
Swapping the source coordinate of a composition product turns `κ.comap fst`
into `κ.comap snd`.
-/
private lemma map_compProd_comap_swap
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  {ν : Measure (α × β)} [SFinite ν]
  {κ : Kernel α γ} [IsSFiniteKernel κ] :
  (ν ⊗ₘ κ.comap Prod.fst (by fun_prop)).map (Prod.map Prod.swap id) =
    ν.map Prod.swap ⊗ₘ κ.comap Prod.snd (by fun_prop) := by
-- proof
  have h :=
    map_compProd_comap_prod (ν := ν) (κ := κ)
      (f := (Prod.fst : α × β → α)) (g := (Prod.snd : α × β → β))
      (by fun_prop) (by fun_prop)
  -- h: (ν ⊗ₘ κ.comap fst).map (Prod.map (fun p => (p.1, p.2)) id) = ν.map (fun p => (p.1, p.2)) ⊗ₘ κ.comap fst
  have hid : (fun p : α × β => (p.1, p.2)) = id := rfl
  have hswap :
    (ν ⊗ₘ κ.comap Prod.fst (by fun_prop)).map (Prod.map Prod.swap id) =
      ((ν ⊗ₘ κ.comap Prod.fst (by fun_prop)).map (Prod.map id id)).map (Prod.map Prod.swap id) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hform :=
    map_compProd_comap_prod (ν := ν.map Prod.swap) (κ := κ)
      (f := (Prod.snd : β × α → α)) (g := (Prod.fst : β × α → β))
      (by fun_prop) (by fun_prop)
  -- Direct evaluation.
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs, Measure.compProd_apply,
    Measure.compProd_apply hs]
  ·
    rw [lintegral_map (Kernel.measurable_kernel_prodMk_left hs) measurable_swap]
    rfl
  ·
    exact (measurable_swap.prodMap measurable_id) hs


/--
`comap` distributes over a composition product.
-/
private lemma comap_compProd
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
  {κ : Kernel α β} [IsSFiniteKernel κ]
  {η : Kernel (α × β) γ} [IsSFiniteKernel η]
  {f : δ → α}
-- given
  (hf : Measurable f) :
-- imply
  (κ ⊗ₖ η).comap f hf =
    κ.comap f hf ⊗ₖ η.comap (Prod.map f id) (by fun_prop) := by
-- proof
  ext x s hs
  rw [Kernel.comap_apply, Kernel.compProd_apply hs, Kernel.compProd_apply hs]
  rfl

/--
Composition of `comap`s is `comap` of the composition.
-/
private lemma kernel_comap_comap
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
  {κ : Kernel α β}
  {f : γ → δ} {g : δ → α}
-- given
  (hf : Measurable f) (hg : Measurable g) :
-- imply
  (κ.comap g hg).comap f hf = κ.comap (g ∘ f) (hg.comp hf) :=
-- proof
  (Kernel.comap_comp_right κ hf hg).symm

/--
The one-step identity of `map_compProd_stageK_K`, with an extra coordinate on the
source that the kernels ignore (`comap Prod.fst` / `comap Prod.snd`).
-/
private lemma map_compProd_stageK_K_fst
  [MeasurableSpace 𝒮] [StandardBorelSpace 𝒮]
  [ReferenceMeasure 𝒜] [MeasurableSpace β]
  {M : Model Θ 𝒮 𝒜} [StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {ν : Measure (𝒮 × β)} [SFinite ν]
-- given
  (θ : Θ) :
-- imply
  ((ν ⊗ₘ (M.stageK θ).comap Prod.fst (by fun_prop)) ⊗ₘ
      (M.K θ).comap Prod.snd (by fun_prop)).map
    (fun p : ((𝒮 × β) × (ℝ × 𝒮 × 𝒜)) × (ℝ × 𝒮 × 𝒜) =>
      (p.1.1, (p.1.2.2.2, p.1.2.1, p.2.2.1))) =
    ν ⊗ₘ
      ((M.stageK θ ⊗ₖ
          M.transK.comap (fun p : 𝒮 × (ℝ × 𝒮 × 𝒜) => p.2.2) (by fun_prop)).map
        (fun p : (ℝ × 𝒮 × 𝒜) × 𝒮 => (p.1.2.2, p.1.1, p.2))).comap
        Prod.fst (by fun_prop) := by
-- proof
  have hid_map :
    (fun p : ((𝒮 × β) × (ℝ × 𝒮 × 𝒜)) × (ℝ × 𝒮 × 𝒜) => (p.1, p.2.2.1)) =
      Prod.map id (fun z : ℝ × 𝒮 × 𝒜 => z.2.1) :=
    rfl
  have hnext :
    ((ν ⊗ₘ (M.stageK θ).comap Prod.fst (by fun_prop)) ⊗ₘ
        (M.K θ).comap Prod.snd (by fun_prop)).map
      (fun p : ((𝒮 × β) × (ℝ × 𝒮 × 𝒜)) × (ℝ × 𝒮 × 𝒜) => (p.1, p.2.2.1)) =
      (ν ⊗ₘ (M.stageK θ).comap Prod.fst (by fun_prop)) ⊗ₘ
        (M.transK.comap (fun z : ℝ × 𝒮 × 𝒜 => z.2) (by fun_prop)).comap
          Prod.snd (by fun_prop) := by
    rw [hid_map, ← Measure.compProd_map (by fun_prop : Measurable (fun z : ℝ × 𝒮 × 𝒜 => z.2.1))]
    rw [← Kernel.comap_map_comm (M.K θ)
      (by fun_prop : Measurable
        (Prod.snd : ((𝒮 × β) × (ℝ × 𝒮 × 𝒜)) → ℝ × 𝒮 × 𝒜))
      (by fun_prop : Measurable (fun z : ℝ × 𝒮 × 𝒜 => z.2.1))]
    rw [map_K_state (M := M) θ]
  have hpush :
    ((ν ⊗ₘ (M.stageK θ).comap Prod.fst (by fun_prop)) ⊗ₘ
        (M.K θ).comap Prod.snd (by fun_prop)).map
      (fun p : ((𝒮 × β) × (ℝ × 𝒮 × 𝒜)) × (ℝ × 𝒮 × 𝒜) =>
        (p.1.1, (p.1.2.2.2, p.1.2.1, p.2.2.1))) =
      ((ν ⊗ₘ (M.stageK θ).comap Prod.fst (by fun_prop)) ⊗ₘ
          (M.transK.comap (fun z : ℝ × 𝒮 × 𝒜 => z.2) (by fun_prop)).comap
            Prod.snd (by fun_prop)).map
        (fun p : ((𝒮 × β) × (ℝ × 𝒮 × 𝒜)) × 𝒮 =>
          (p.1.1, (p.1.2.2.2, p.1.2.1, p.2))) := by
    have h :=
      congrArg
        (Measure.map
          (fun p : ((𝒮 × β) × (ℝ × 𝒮 × 𝒜)) × 𝒮 =>
            (p.1.1, (p.1.2.2.2, p.1.2.1, p.2))))
        hnext
    rw [Measure.map_map (by fun_prop) (by fun_prop)] at h
    have hfun :
      (fun p : ((𝒮 × β) × (ℝ × 𝒮 × 𝒜)) × (ℝ × 𝒮 × 𝒜) =>
          (p.1.1, (p.1.2.2.2, p.1.2.1, p.2.2.1))) =
        (fun p : ((𝒮 × β) × (ℝ × 𝒮 × 𝒜)) × 𝒮 =>
            (p.1.1, (p.1.2.2.2, p.1.2.1, p.2))) ∘
          fun p => (p.1, p.2.2.1) :=
      rfl
    rw [hfun]
    exact h
  have hη :
    ((M.transK.comap (fun z : ℝ × 𝒮 × 𝒜 => z.2) (by fun_prop)).comap
        Prod.snd (by fun_prop)) =
      M.transK.comap
        (fun p : ((𝒮 × β) × (ℝ × 𝒮 × 𝒜)) => p.2.2) (by fun_prop) := by
    rw [kernel_comap_comap]
    rfl
  rw [hη] at hpush
  have hassoc :=
    Measure.compProd_assoc'
      (μ := ν)
      (κ := (M.stageK θ).comap Prod.fst (by fun_prop))
      (η := M.transK.comap
        (fun p : ((𝒮 × β) × (ℝ × 𝒮 × 𝒜)) => p.2.2) (by fun_prop))
  have hkernel :
    (M.stageK θ).comap Prod.fst (by fun_prop) ⊗ₖ
        M.transK.comap (fun p : ((𝒮 × β) × (ℝ × 𝒮 × 𝒜)) => p.2.2) (by fun_prop) =
      (M.stageK θ ⊗ₖ
          M.transK.comap (fun p : 𝒮 × (ℝ × 𝒮 × 𝒜) => p.2.2) (by fun_prop)).comap
        Prod.fst (by fun_prop) := by
    rw [comap_compProd, kernel_comap_comap]
    rfl
  have hident :
    ((ν ⊗ₘ (M.stageK θ).comap Prod.fst (by fun_prop)) ⊗ₘ
        M.transK.comap (fun p : ((𝒮 × β) × (ℝ × 𝒮 × 𝒜)) => p.2.2) (by fun_prop)).map
      (fun p : ((𝒮 × β) × (ℝ × 𝒮 × 𝒜)) × 𝒮 =>
        (p.1.1, (p.1.2.2.2, p.1.2.1, p.2))) =
      (ν ⊗ₘ
          ((M.stageK θ ⊗ₖ
              M.transK.comap (fun p : 𝒮 × (ℝ × 𝒮 × 𝒜) => p.2.2) (by fun_prop)).comap
            Prod.fst (by fun_prop))).map
        (fun q : (𝒮 × β) × ((ℝ × 𝒮 × 𝒜) × 𝒮) =>
          (q.1, (q.2.1.2.2, q.2.1.1, q.2.2))) := by
    have h :=
      congrArg
        (Measure.map
          (fun q : (𝒮 × β) × ((ℝ × 𝒮 × 𝒜) × 𝒮) =>
            (q.1, (q.2.1.2.2, q.2.1.1, q.2.2))))
        hassoc
    rw [Measure.map_map (by fun_prop) (by fun_prop), hkernel] at h
    have hfun :
      (fun p : ((𝒮 × β) × (ℝ × 𝒮 × 𝒜)) × 𝒮 =>
          (p.1.1, (p.1.2.2.2, p.1.2.1, p.2))) =
        (fun q : (𝒮 × β) × ((ℝ × 𝒮 × 𝒜) × 𝒮) =>
            (q.1, (q.2.1.2.2, q.2.1.1, q.2.2))) ∘
          ⇑MeasurableEquiv.prodAssoc :=
      rfl
    rw [hfun]
    exact h
  have hmapκ :
    (ν ⊗ₘ
        ((M.stageK θ ⊗ₖ
            M.transK.comap (fun p : 𝒮 × (ℝ × 𝒮 × 𝒜) => p.2.2) (by fun_prop)).comap
          Prod.fst (by fun_prop))).map
      (fun q : (𝒮 × β) × ((ℝ × 𝒮 × 𝒜) × 𝒮) =>
        (q.1, (q.2.1.2.2, q.2.1.1, q.2.2))) =
      ν ⊗ₘ
        ((M.stageK θ ⊗ₖ
            M.transK.comap (fun p : 𝒮 × (ℝ × 𝒮 × 𝒜) => p.2.2) (by fun_prop)).map
          (fun p : (ℝ × 𝒮 × 𝒜) × 𝒮 => (p.1.2.2, p.1.1, p.2))).comap
          Prod.fst (by fun_prop) := by
    have hfun :
      (fun q : (𝒮 × β) × ((ℝ × 𝒮 × 𝒜) × 𝒮) =>
          (q.1, (q.2.1.2.2, q.2.1.1, q.2.2))) =
        Prod.map id (fun p : (ℝ × 𝒮 × 𝒜) × 𝒮 => (p.1.2.2, p.1.1, p.2)) :=
      rfl
    rw [hfun, ← Measure.compProd_map (by fun_prop)]
    rw [← Kernel.comap_map_comm
      (M.stageK θ ⊗ₖ M.transK.comap (fun p : 𝒮 × (ℝ × 𝒮 × 𝒜) => p.2.2) (by fun_prop))
      (by fun_prop : Measurable (Prod.fst : 𝒮 × β → 𝒮))
      (by fun_prop)]
  exact hpush.trans (hident.trans hmapκ)


/--
History irrelevance (one-step Markov property) of the continuous-action trajectory model `M θ`
(`Model`): given the current state `s n`, the next step `(a n, r n, s (n + 1))` is
conditionally independent of the history `(r, s, a)[:n]`.
Built into the Ionescu-Tulcea construction: `Model.step` only reads the last stage, and
the policy and environment are Markov (they do not read history).
Feeds `Random.CondIndep.of.All_CondIndep.All_MeasurableJoint`.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [StandardBorelSpace 𝒮] [Nonempty 𝒮]
  [ReferenceMeasure 𝒜] [StandardBorelSpace 𝒜] [Nonempty 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {θ : Θ}
  {n : ℕ}
-- given
  (h₀ : ∀ t, (· t) = (r t, s t, a t)) :
-- imply
  let h : ∀ t, Measurable (r t, s t, a t) := fun t ↦ (h₀ t) ▸ measurable_pi_apply t;
  (a n, r n, s (n + 1)) ⟂ᵢ[M θ] (r, s, a)[:n] | s n := by
-- proof
  intro h
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₀ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₀ t) ω)).symm
  let μ := M θ
  let Sn : (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 := fun ω => (ω n).2.1
  let Y : (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜 × ℝ × 𝒮 :=
    fun ω => ((ω n).2.2, (ω n).1, (ω (n + 1)).2.1)
  let Z : (ℕ → ℝ × 𝒮 × 𝒜) → (Fin n → ℝ × 𝒮 × 𝒜) := fun ω i => ω (i : ℕ)
  let κ : Kernel 𝒮 (𝒜 × ℝ × 𝒮) :=
    (M.stageK θ ⊗ₖ M.transK.comap (fun p : 𝒮 × (ℝ × 𝒮 × 𝒜) => p.2.2) (by fun_prop)).map
      (fun p : (ℝ × 𝒮 × 𝒜) × 𝒮 => (p.1.2.2, p.1.1, p.2))
  have hSn : Measurable Sn := by fun_prop
  have hY : Measurable Y := by fun_prop
  have hZ : Measurable Z := by fun_prop
  have hSY :
    μ.map (fun ω => (Sn ω, Y ω)) = μ.map Sn ⊗ₘ κ := by
    have hpair := Map.eq.CompProd.of.All_EqWithDensity (M := M) θ n
    have hstage :=
      Map.eq.BindStageK.of.All_Eq_Joint.All_EqWithDensity (M := M) h₀ θ n
    have hmap :=
      congrArg
        (Measure.map
          (fun p : (ℝ × 𝒮 × 𝒜) × (ℝ × 𝒮 × 𝒜) => (p.1.2.1, (p.1.2.2, p.1.1, p.2.2.1))))
        hpair
    have hL :
      Measure.map
          (fun p : (ℝ × 𝒮 × 𝒜) × (ℝ × 𝒮 × 𝒜) => (p.1.2.1, (p.1.2.2, p.1.1, p.2.2.1)))
          (μ.map (fun ω => (ω n, ω (n + 1)))) =
        μ.map (fun ω => (Sn ω, Y ω)) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    have hR :
      Measure.map
          (fun p : (ℝ × 𝒮 × 𝒜) × (ℝ × 𝒮 × 𝒜) => (p.1.2.1, (p.1.2.2, p.1.1, p.2.2.1)))
          (μ.map (fun ω => ω n) ⊗ₘ M.K θ) =
        μ.map Sn ⊗ₘ κ := by
      rw [hstage]
      exact map_compProd_stageK_K (M := M) (ν := μ.map Sn) θ
    exact hL.symm.trans (hmap.trans hR)
  have hSZY :
    μ.map (fun ω => ((Sn ω, Z ω), Y ω)) =
      μ.map (fun ω => (Sn ω, Z ω)) ⊗ₘ κ.comap Prod.fst (by fun_prop) := by
    cases n with
    | zero =>
      let constZ : Fin 0 → ℝ × 𝒮 × 𝒜 := fun i => i.elim0
      have hZconst : Z = fun _ => constZ := by
        funext ω
        funext i
        exact i.elim0
      have hmap :=
        congrArg
          (Measure.map (fun p : 𝒮 × (𝒜 × ℝ × 𝒮) => ((p.1, constZ), p.2)))
          hSY
      have hL :
        Measure.map (fun p : 𝒮 × (𝒜 × ℝ × 𝒮) => ((p.1, constZ), p.2))
            (μ.map (fun ω => (Sn ω, Y ω))) =
          μ.map (fun ω => ((Sn ω, Z ω), Y ω)) := by
        rw [hZconst, Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
      have hR :
        Measure.map (fun p : 𝒮 × (𝒜 × ℝ × 𝒮) => ((p.1, constZ), p.2))
            (μ.map Sn ⊗ₘ κ) =
          μ.map (fun ω => (Sn ω, Z ω)) ⊗ₘ κ.comap Prod.fst (by fun_prop) := by
        have hform :=
          map_compProd_comap_prod (ν := μ.map Sn) (κ := κ)
            (f := (id : 𝒮 → 𝒮)) (g := fun _ : 𝒮 => constZ)
            measurable_id (by fun_prop)
        have hid : κ.comap (id : 𝒮 → 𝒮) measurable_id = κ := Kernel.comap_id _
        have hZmap :
          μ.map (fun ω => (Sn ω, Z ω)) = (μ.map Sn).map (fun y => (y, constZ)) := by
          rw [hZconst, Measure.map_map (by fun_prop) hSn]
          rfl
        have hfun :
          (fun p : 𝒮 × (𝒜 × ℝ × 𝒮) => ((p.1, constZ), p.2)) =
            Prod.map (fun y : 𝒮 => (y, constZ)) id :=
          rfl
        rw [hid] at hform
        rw [hZmap, hfun]
        exact hform
      exact hL.symm.trans (hmap.trans hR)
    | succ m =>
      let H := Preorder.frestrictLe (π := fun _ : ℕ => ℝ × 𝒮 × 𝒜) m
      let e : (Π _ : Finset.Iic m, ℝ × 𝒮 × 𝒜) → ℝ × 𝒮 × 𝒜 :=
        fun hist => hist ⟨m, mem_Iic.2 le_rfl⟩
      have he : Measurable e := measurable_pi_apply _
      let Z_of : (Π _ : Finset.Iic m, ℝ × 𝒮 × 𝒜) → (Fin (m + 1) → ℝ × 𝒮 × 𝒜) :=
        fun hist i => hist ⟨i, mem_Iic.2 (Nat.lt_succ_iff.mp i.isLt)⟩
      have hZof : Measurable Z_of := by fun_prop
      let μ₀ : Measure (ℝ × 𝒮 × 𝒜) := M.stageK θ ∘ₘ (M.init : Measure _)
      have hH_n :
        μ.map (fun ω => (H ω, ω (m + 1))) =
          μ.map H ⊗ₘ (M.K θ).comap e he := by
        have hIT :=
          Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
            (X := fun _ ↦ ℝ × 𝒮 × 𝒜) (μ₀ := μ₀) (κ := M.step θ) (a := m)
        have hstep : M.step θ m = (M.K θ).comap e he := rfl
        unfold μ Model.traj H
        rw [← hstep]
        exact hIT.symm
      have hHist_n :
        μ.map (fun ω => ((Sn ω, Z ω), ω (m + 1))) =
          μ.map (fun ω => (Sn ω, Z ω)) ⊗ₘ
            (M.stageK θ).comap Prod.fst (by fun_prop) := by
        have hmap :=
          congrArg
            (Measure.map
              (fun p : (Π _ : Finset.Iic m, ℝ × 𝒮 × 𝒜) × (ℝ × 𝒮 × 𝒜) =>
                ((p.2.2.1, Z_of p.1), p.2)))
            hH_n
        have hL :
          Measure.map
              (fun p : (Π _ : Finset.Iic m, ℝ × 𝒮 × 𝒜) × (ℝ × 𝒮 × 𝒜) =>
                ((p.2.2.1, Z_of p.1), p.2))
              (μ.map (fun ω => (H ω, ω (m + 1)))) =
            μ.map (fun ω => ((Sn ω, Z ω), ω (m + 1))) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          rfl
        have h1 :
          (μ.map H ⊗ₘ (M.K θ).comap e he).map
              (fun p : (Π _ : Finset.Iic m, ℝ × 𝒮 × 𝒜) × (ℝ × 𝒮 × 𝒜) =>
                ((p.2.2.1, Z_of p.1), p.2)) =
            (μ.map H ⊗ₘ ((M.K θ).map (fun z => (z.2.1, z))).comap e he).map
              (fun q : (Π _ : Finset.Iic m, ℝ × 𝒮 × 𝒜) × (𝒮 × ℝ × 𝒮 × 𝒜) =>
                ((q.2.1, Z_of q.1), q.2.2)) := by
          have hcp :=
            Measure.compProd_map (μ := μ.map H) (κ := (M.K θ).comap e he)
              (f := fun z : ℝ × 𝒮 × 𝒜 => (z.2.1, z)) (by fun_prop)
          have hfun :
            (fun p : (Π _ : Finset.Iic m, ℝ × 𝒮 × 𝒜) × (ℝ × 𝒮 × 𝒜) =>
                ((p.2.2.1, Z_of p.1), p.2)) =
              (fun q : (Π _ : Finset.Iic m, ℝ × 𝒮 × 𝒜) × (𝒮 × ℝ × 𝒮 × 𝒜) =>
                ((q.2.1, Z_of q.1), q.2.2)) ∘
                Prod.map id (fun z : ℝ × 𝒮 × 𝒜 => (z.2.1, z)) :=
            rfl
          rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop), ← hcp]
          rw [← Kernel.comap_map_comm (M.K θ) he (by fun_prop)]
        have hSZ :
          μ.map (fun ω => (Sn ω, Z ω)) =
            (μ.map H ⊗ₘ M.transK.comap (fun hist => (e hist).2) (by fun_prop)).map
              (fun q => (q.2, Z_of q.1)) := by
          have hnext :=
            congrArg
              (Measure.map
                (fun p : (Π _ : Finset.Iic m, ℝ × 𝒮 × 𝒜) × (ℝ × 𝒮 × 𝒜) =>
                  (p.2.2.1, Z_of p.1)))
              hH_n
          have hL' :
            Measure.map
                (fun p : (Π _ : Finset.Iic m, ℝ × 𝒮 × 𝒜) × (ℝ × 𝒮 × 𝒜) =>
                  (p.2.2.1, Z_of p.1))
                (μ.map (fun ω => (H ω, ω (m + 1)))) =
              μ.map (fun ω => (Sn ω, Z ω)) := by
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
            rfl
          have hR' :
            Measure.map
                (fun p : (Π _ : Finset.Iic m, ℝ × 𝒮 × 𝒜) × (ℝ × 𝒮 × 𝒜) =>
                  (p.2.2.1, Z_of p.1))
                (μ.map H ⊗ₘ (M.K θ).comap e he) =
              (μ.map H ⊗ₘ M.transK.comap (fun hist => (e hist).2) (by fun_prop)).map
                (fun q => (q.2, Z_of q.1)) := by
            have hcp :=
              Measure.compProd_map (μ := μ.map H) (κ := (M.K θ).comap e he)
                (f := fun z : ℝ × 𝒮 × 𝒜 => z.2.1) (by fun_prop)
            have hfun :
              (fun p : (Π _ : Finset.Iic m, ℝ × 𝒮 × 𝒜) × (ℝ × 𝒮 × 𝒜) =>
                  (p.2.2.1, Z_of p.1)) =
                (fun q : (Π _ : Finset.Iic m, ℝ × 𝒮 × 𝒜) × 𝒮 => (q.2, Z_of q.1)) ∘
                  Prod.map id (fun z : ℝ × 𝒮 × 𝒜 => z.2.1) :=
              rfl
            have hcomm :
              ((M.K θ).comap e he).map (fun z : ℝ × 𝒮 × 𝒜 => z.2.1) =
                M.transK.comap (fun hist => (e hist).2) (by fun_prop) := by
              rw [← Kernel.comap_map_comm (M.K θ) he (by fun_prop),
                map_K_state (M := M) θ, kernel_comap_comap]
              rfl
            rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop), ← hcp, hcomm]
          exact hL'.symm.trans (hnext.trans hR')
        have hdone :
          (μ.map H ⊗ₘ ((M.K θ).map (fun z => (z.2.1, z))).comap e he).map
              (fun q : (Π _ : Finset.Iic m, ℝ × 𝒮 × 𝒜) × (𝒮 × ℝ × 𝒮 × 𝒜) =>
                ((q.2.1, Z_of q.1), q.2.2)) =
            μ.map (fun ω => (Sn ω, Z ω)) ⊗ₘ
              (M.stageK θ).comap Prod.fst (by fun_prop) := by
          rw [map_K_prod (M := M) θ, comap_compProd]
          have hη :
            (M.transK.comap (fun z => z.2) (by fun_prop)).comap e he =
              M.transK.comap (fun hist => (e hist).2) (by fun_prop) := by
            rw [kernel_comap_comap]
            rfl
          have hη' :
            ((M.stageK θ).comap Prod.snd (by fun_prop)).comap (Prod.map e id) (by fun_prop) =
              (M.stageK θ).comap Prod.snd (by fun_prop) := by
            rw [kernel_comap_comap]
            rfl
          rw [hη, hη']
          have hμ :
            (μ.map H ⊗ₘ
                (M.transK.comap (fun hist => (e hist).2) (by fun_prop) ⊗ₖ
                  (M.stageK θ).comap Prod.snd (by fun_prop))).map
                (fun q : (Π _ : Finset.Iic m, ℝ × 𝒮 × 𝒜) × (𝒮 × ℝ × 𝒮 × 𝒜) =>
                  ((q.2.1, Z_of q.1), q.2.2)) =
              (μ.map H ⊗ₘ M.transK.comap (fun hist => (e hist).2) (by fun_prop) ⊗ₘ
                  (M.stageK θ).comap Prod.snd (by fun_prop)).map
                (fun q : ((Π _ : Finset.Iic m, ℝ × 𝒮 × 𝒜) × 𝒮) × (ℝ × 𝒮 × 𝒜) =>
                  ((q.1.2, Z_of q.1.1), q.2)) := by
            have h :=
              congrArg
                (Measure.map
                  (fun q : ((Π _ : Finset.Iic m, ℝ × 𝒮 × 𝒜) × 𝒮) × (ℝ × 𝒮 × 𝒜) =>
                    ((q.1.2, Z_of q.1.1), q.2)))
                (Measure.compProd_assoc
                  (μ := μ.map H)
                  (κ := M.transK.comap (fun hist => (e hist).2) (by fun_prop))
                  (η := (M.stageK θ).comap Prod.snd (by fun_prop)))
            rw [Measure.map_map (by fun_prop) (by fun_prop)] at h
            have hfun :
              (fun q : (Π _ : Finset.Iic m, ℝ × 𝒮 × 𝒜) × (𝒮 × ℝ × 𝒮 × 𝒜) =>
                  ((q.2.1, Z_of q.1), q.2.2)) =
                (fun q : ((Π _ : Finset.Iic m, ℝ × 𝒮 × 𝒜) × 𝒮) × (ℝ × 𝒮 × 𝒜) =>
                    ((q.1.2, Z_of q.1.1), q.2)) ∘
                  ⇑MeasurableEquiv.prodAssoc.symm :=
              rfl
            rw [hfun]
            exact h
          have hform :=
            map_compProd_comap_prod
              (ν := μ.map H ⊗ₘ M.transK.comap (fun hist => (e hist).2) (by fun_prop))
              (κ := M.stageK θ)
              (f := fun q : (Π _ : Finset.Iic m, ℝ × 𝒮 × 𝒜) × 𝒮 => q.2)
              (g := fun q => Z_of q.1)
              (by fun_prop) (by fun_prop)
          have hfun :
            (fun q : ((Π _ : Finset.Iic m, ℝ × 𝒮 × 𝒜) × 𝒮) × (ℝ × 𝒮 × 𝒜) =>
                ((q.1.2, Z_of q.1.1), q.2)) =
              Prod.map (fun q : (Π _ : Finset.Iic m, ℝ × 𝒮 × 𝒜) × 𝒮 => (q.2, Z_of q.1)) id :=
            rfl
          exact (hμ.trans (hfun ▸ hform)).trans (by rw [← hSZ])
        exact hL.symm.trans (hmap.trans (h1.trans hdone))
      let Hn := Preorder.frestrictLe (π := fun _ : ℕ => ℝ × 𝒮 × 𝒜) (m + 1)
      let en : (Π _ : Finset.Iic (m + 1), ℝ × 𝒮 × 𝒜) → ℝ × 𝒮 × 𝒜 :=
        fun hist => hist ⟨m + 1, mem_Iic.2 le_rfl⟩
      have hen : Measurable en := measurable_pi_apply _
      let Z_of_n : (Π _ : Finset.Iic (m + 1), ℝ × 𝒮 × 𝒜) → (Fin (m + 1) → ℝ × 𝒮 × 𝒜) :=
        fun hist i => hist ⟨i, mem_Iic.2 (Nat.le_of_lt i.isLt)⟩
      have hHn :
        μ.map (fun ω => (Hn ω, ω (m + 1 + 1))) =
          μ.map Hn ⊗ₘ (M.K θ).comap en hen := by
        have hIT :=
          Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
            (X := fun _ ↦ ℝ × 𝒮 × 𝒜) (μ₀ := μ₀) (κ := M.step θ) (a := m + 1)
        have hstep : M.step θ (m + 1) = (M.K θ).comap en hen := rfl
        unfold μ Model.traj Hn
        rw [← hstep]
        exact hIT.symm
      have hnext :
        μ.map (fun ω => (((Sn ω, Z ω), ω (m + 1)), ω (m + 1 + 1))) =
          μ.map (fun ω => ((Sn ω, Z ω), ω (m + 1))) ⊗ₘ
            (M.K θ).comap Prod.snd (by fun_prop) := by
        let g : (Π _ : Finset.Iic (m + 1), ℝ × 𝒮 × 𝒜) →
            𝒮 × (Fin (m + 1) → ℝ × 𝒮 × 𝒜) :=
          fun hist => ((en hist).2.1, Z_of_n hist)
        have hg : Measurable g := by fun_prop
        have hform :=
          map_compProd_comap_prod (ν := μ.map Hn) (κ := M.K θ)
            (f := en) (g := g) hen hg
        have hswap :=
          map_compProd_comap_swap (ν := (μ.map Hn).map (fun hist => (en hist, g hist)))
            (κ := M.K θ)
        have hmap := congrArg (Measure.map (Prod.map (fun hist => (g hist, en hist)) id)) hHn
        have hL :
          Measure.map (Prod.map (fun hist => (g hist, en hist)) id)
              (μ.map (fun ω => (Hn ω, ω (m + 1 + 1)))) =
            μ.map (fun ω => (((Sn ω, Z ω), ω (m + 1)), ω (m + 1 + 1))) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          rfl
        have hR :
          Measure.map (Prod.map (fun hist => (g hist, en hist)) id)
              (μ.map Hn ⊗ₘ (M.K θ).comap en hen) =
            μ.map (fun ω => ((Sn ω, Z ω), ω (m + 1))) ⊗ₘ
              (M.K θ).comap Prod.snd (by fun_prop) := by
          have hfun :
            (fun hist => (g hist, en hist)) =
              Prod.swap ∘ fun hist => (en hist, g hist) :=
            rfl
          have h1 :
            (μ.map Hn ⊗ₘ (M.K θ).comap en hen).map
                (Prod.map (fun hist => (g hist, en hist)) id) =
              ((μ.map Hn ⊗ₘ (M.K θ).comap en hen).map
                  (Prod.map (fun hist => (en hist, g hist)) id)).map
                (Prod.map Prod.swap id) := by
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
            rfl
          have h2 :
            ((μ.map Hn).map (fun hist => (en hist, g hist))).map Prod.swap =
              μ.map (fun ω => ((Sn ω, Z ω), ω (m + 1))) := by
            rw [Measure.map_map measurable_swap (by fun_prop), Measure.map_map (by fun_prop)
              (by fun_prop)]
            rfl
          rw [h1, hform, map_compProd_comap_swap, h2]
        exact hL.symm.trans (hmap.trans hR)
      have hYmap :=
        congrArg
          (Measure.map
            (fun p : ((𝒮 × (Fin (m + 1) → ℝ × 𝒮 × 𝒜)) × (ℝ × 𝒮 × 𝒜)) × (ℝ × 𝒮 × 𝒜) =>
              (p.1.1, (p.1.2.2.2, p.1.2.1, p.2.2.1))))
          hnext
      have hLY :
        Measure.map
            (fun p : ((𝒮 × (Fin (m + 1) → ℝ × 𝒮 × 𝒜)) × (ℝ × 𝒮 × 𝒜)) × (ℝ × 𝒮 × 𝒜) =>
              (p.1.1, (p.1.2.2.2, p.1.2.1, p.2.2.1)))
            (μ.map (fun ω => (((Sn ω, Z ω), ω (m + 1)), ω (m + 1 + 1)))) =
          μ.map (fun ω => ((Sn ω, Z ω), Y ω)) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        rfl
      have hRY :
        Measure.map
            (fun p : ((𝒮 × (Fin (m + 1) → ℝ × 𝒮 × 𝒜)) × (ℝ × 𝒮 × 𝒜)) × (ℝ × 𝒮 × 𝒜) =>
              (p.1.1, (p.1.2.2.2, p.1.2.1, p.2.2.1)))
            (μ.map (fun ω => ((Sn ω, Z ω), ω (m + 1))) ⊗ₘ
              (M.K θ).comap Prod.snd (by fun_prop)) =
          μ.map (fun ω => (Sn ω, Z ω)) ⊗ₘ κ.comap Prod.fst (by fun_prop) := by
        rw [hHist_n]
        exact map_compProd_stageK_K_fst (M := M)
          (ν := μ.map (fun ω => (Sn ω, Z ω))) θ
      exact hLY.symm.trans (hYmap.trans hRY)
  have hcd_SZ :
    condDistrib Y (fun ω => (Sn ω, Z ω)) μ =ᵐ[μ.map (fun ω => (Sn ω, Z ω))]
      κ.comap Prod.fst (by fun_prop) :=
    condDistrib_ae_eq_of_measure_eq_compProd (by fun_prop) hY.aemeasurable hSZY
  have hcd_S : condDistrib Y Sn μ =ᵐ[μ.map Sn] κ :=
    condDistrib_ae_eq_of_measure_eq_compProd (by fun_prop) hY.aemeasurable hSY
  apply CondIndepFun.symm
  dsimp only [JointRandomSymbol, Function.getSlice, Fun.getSlice, getElem]
  change Z ⟂ᵢ[Sn, hSn; μ] Y
  rw [condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight hY hZ hSn]
  refine hcd_SZ.trans ?_
  change
    (fun p => κ p.1) =ᵐ[μ.map (fun ω => (Sn ω, Z ω))]
      (fun p => condDistrib Y Sn μ p.1)
  apply ae_eq_comp measurable_fst.aemeasurable
  convert hcd_S.symm
  rw [Measure.map_map measurable_fst (hSn.prodMk hZ)]
  apply congrArg (fun f => Measure.map f μ)
  ext1
  rfl


-- created on 2026-11-04
-- updated on 2026-11-18
