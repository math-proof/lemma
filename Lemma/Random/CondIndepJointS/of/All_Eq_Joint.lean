import Lemma.Random.Map.eq.BindStageK.of.All_EqWithDensity
import Lemma.Measure.MapComap_MapId.eq.Map.of.Measurable
import Def.Probability.Process.HiddenMarkovSequence.Part2
import Notation.Probability.JointRv
import Notation.Fun
import Class.Dynamics.MarkovDecisionProcess
import Instance.Dynamics.PolicyTrajectory
import Initialize.Tactic.Attr.Basic
import Instance.Data.Nat.Fun
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
The next state of a stage is drawn from the transition kernel of the current
state-action pair: `(K θ).map (·.2.1) = transK.comap (·.2)`.
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
  have hsk :
    (M.stageK θ).map (fun z : ℝ × 𝒮 × 𝒜 => z.2.1) =
      Kernel.deterministic (id : 𝒮 → 𝒮) measurable_id := by
    unfold Model.stageK
    rw [← Kernel.map_comp_right _ (by fun_prop) (by fun_prop)]
    show (Kernel.deterministic id measurable_id ×ₖ (M.kernel θ ⊗ₖ M.rewardK)).map Prod.fst = _
    rw [← Kernel.fst_eq]
    exact Kernel.fst_prod _ _
  unfold Model.K
  rw [Kernel.map_comp, hsk, Kernel.deterministic_comp_eq_map measurable_id, Kernel.map_id]

/-- `(Kernel.comp κ η).comap f = Kernel.comp κ (η.comap f)`. -/
private lemma comp_comap
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
  {κ : Kernel β γ} [IsSFiniteKernel κ]
  {η : Kernel α β} [IsSFiniteKernel η]
  {f : δ → α}
-- given
  (hf : Measurable f) :
-- imply
  (Kernel.comp κ η).comap f hf = Kernel.comp κ (η.comap f hf) := by
-- proof
  ext a
  rw [Kernel.comap_apply, Kernel.comp_apply, Kernel.comp_apply, Kernel.comap_apply]

/--
The state-action component of `stageK θ` is `δ_s × π_θ(· | s)`.
-/
private lemma map_stageK_sa
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
-- given
  (θ : Θ) :
-- imply
  (M.stageK θ).map (fun z : ℝ × 𝒮 × 𝒜 => z.2) =
    Kernel.deterministic (id : 𝒮 → 𝒮) measurable_id ×ₖ M.kernel θ := by
-- proof
  unfold Model.stageK
  rw [← Kernel.map_comp_right _ (by fun_prop) (by fun_prop)]
  change
    (Kernel.deterministic (id : 𝒮 → 𝒮) measurable_id ×ₖ (M.kernel θ ⊗ₖ M.rewardK)).map
      (fun z : 𝒮 × 𝒜 × ℝ => (z.1, z.2.1)) =
    Kernel.deterministic (id : 𝒮 → 𝒮) measurable_id ×ₖ M.kernel θ
  rw [show (fun z : 𝒮 × 𝒜 × ℝ => (z.1, z.2.1)) = Prod.map id Prod.fst from rfl,
    ← Kernel.map_prod_map _ _ measurable_id measurable_fst, Kernel.map_id]
  have hfst : (M.kernel θ ⊗ₖ M.rewardK).map Prod.fst = M.kernel θ := by
    rw [← Kernel.fst_eq]
    exact Kernel.fst_compProd _ _
  rw [hfst]

/--
Given the current state, `stageK` samples `(a, r)` from `π_θ(· | s)` and
`reward (s, a)`, so the law of `((s, a), r)` factors through `rewardK`.
-/
private lemma map_stageK_reward
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
-- given
  (θ : Θ)
  (x : 𝒮) :
-- imply
  (M.stageK θ x).map (fun z : ℝ × 𝒮 × 𝒜 => (z.2, z.1)) =
    (M.stageK θ x).map (fun z => z.2) ⊗ₘ M.rewardK := by
-- proof
  have hφ : Measurable fun z : ℝ × 𝒮 × 𝒜 => (z.2, z.1) := by fun_prop
  have hψ : Measurable fun z : ℝ × 𝒮 × 𝒜 => z.2 := by fun_prop
  have hsa : (M.stageK θ x).map (fun z => z.2) =
      (Measure.dirac x).prod (M.kernel θ x) := by
    rw [← Kernel.map_apply _ hψ, map_stageK_sa (M := M) θ, Kernel.prod_apply,
      Kernel.deterministic_apply measurable_id]
    rfl
  have hκ :
    (M.kernel θ ⊗ₖ M.rewardK) x =
      (M.kernel θ x) ⊗ₘ (M.rewardK.comap (Prod.mk x) measurable_prodMk_left) := by
    ext t ht
    rw [Kernel.compProd_apply ht, Measure.compProd_apply ht]
    rfl
  rw [hsa]
  ext s hs
  have hL :
    (M.stageK θ x).map (fun z => (z.2, z.1)) s =
      ∫⁻ a, M.rewardK (x, a) (Prod.mk (x, a) ⁻¹' s) ∂(M.kernel θ x) := by
    unfold Model.stageK
    rw [Kernel.map_apply _ (by fun_prop), Measure.map_map hφ (by fun_prop),
      Measure.map_apply (by fun_prop) hs, Kernel.prod_apply,
      Kernel.deterministic_apply measurable_id]
    have hset :
      ((fun z => (z.2, z.1)) ∘ fun z => (z.2.2, z.1, z.2.1)) ⁻¹' s =
        {z : 𝒮 × 𝒜 × ℝ | ((z.1, z.2.1), z.2.2) ∈ s} :=
      rfl
    have hmeasZ :
      Measurable fun z : 𝒮 × 𝒜 × ℝ => ((z.1, z.2.1), z.2.2) := by
      fun_prop
    have hz : MeasurableSet {z : 𝒮 × 𝒜 × ℝ | ((z.1, z.2.1), z.2.2) ∈ s} :=
      hmeasZ hs
    have hmeasQR :
      Measurable fun qr : 𝒜 × ℝ => ((x, qr.1), qr.2) := by
      fun_prop
    rw [hset, Measure.prod_apply hz, lintegral_dirac']
    ·
      have hset2 :
        Prod.mk (id x) ⁻¹' {z : 𝒮 × 𝒜 × ℝ | ((z.1, z.2.1), z.2.2) ∈ s} =
          (fun qr : 𝒜 × ℝ => ((x, qr.1), qr.2)) ⁻¹' s :=
        rfl
      rw [hκ, hset2, Measure.compProd_apply (hmeasQR hs)]
      refine lintegral_congr fun a => ?_
      rw [Kernel.comap_apply]
      rfl
    ·
      exact measurable_measure_prodMk_left hz
  apply hL.trans
  have hf :
    Measurable fun z : 𝒮 × 𝒜 => M.rewardK z (Prod.mk z ⁻¹' s) :=
    Kernel.measurable_kernel_prodMk_left hs
  have hfx :
    Measurable fun x_1 : 𝒮 =>
      ∫⁻ a, M.rewardK (x_1, a) (Prod.mk (x_1, a) ⁻¹' s) ∂(M.kernel θ x) :=
    Measurable.lintegral_prod_right hf
  rw [Measure.compProd_apply hs, lintegral_prod _ hf.aemeasurable,
    ← lintegral_dirac' (a := x) hfx]

/--
A mixture of `stageK` still factors `((s, a), r)` through `rewardK`.
-/
private lemma map_bind_stageK_reward
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {ν : Measure 𝒮} [SFinite ν]
-- given
  (θ : Θ) :
-- imply
  (M.stageK θ ∘ₘ ν).map (fun z : ℝ × 𝒮 × 𝒜 => (z.2, z.1)) =
    (M.stageK θ ∘ₘ ν).map (fun z => z.2) ⊗ₘ M.rewardK := by
-- proof
  have hφ : Measurable fun z : ℝ × 𝒮 × 𝒜 => (z.2, z.1) := by fun_prop
  have hψ : Measurable fun z : ℝ × 𝒮 × 𝒜 => z.2 := by fun_prop
  rw [Measure.map_comp _ _ hφ, Measure.map_comp _ _ hψ]
  ext s hs
  have hf : Measurable fun p => M.rewardK p (Prod.mk p ⁻¹' s) :=
    Kernel.measurable_kernel_prodMk_left hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), Measure.compProd_apply hs,
    lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable]
  refine lintegral_congr fun x => ?_
  rw [Kernel.map_apply _ hφ, Kernel.map_apply _ hψ, ← Measure.compProd_apply hs]
  exact congrArg (fun μ => μ s) (map_stageK_reward (M := M) θ x)

/--
The `rewardK` factorization of `stageK`, with a constant coordinate adjoined to
`(s, a)`.
-/
private lemma map_stageK_reward_prod
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜] [MeasurableSpace β]
  {M : Model Θ 𝒮 𝒜} [StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {c : β}
-- given
  (θ : Θ)
  (x : 𝒮) :
-- imply
  (M.stageK θ x).map (fun z : ℝ × 𝒮 × 𝒜 => ((z.2, c), z.1)) =
    (M.stageK θ x).map (fun z => (z.2, c)) ⊗ₘ
      M.rewardK.comap Prod.fst (by fun_prop) := by
-- proof
  have hφ : Measurable fun z : ℝ × 𝒮 × 𝒜 => (z.2, z.1) := by fun_prop
  have hψ : Measurable fun z : ℝ × 𝒮 × 𝒜 => z.2 := by fun_prop
  have hL :
    (M.stageK θ x).map (fun z => ((z.2, c), z.1)) =
      ((M.stageK θ x).map (fun z => (z.2, z.1))).map (fun p => ((p.1, c), p.2)) := by
    rw [Measure.map_map (by fun_prop) hφ]
    rfl
  have hR :
    (M.stageK θ x).map (fun z => (z.2, c)) =
      ((M.stageK θ x).map (fun z => z.2)).map (fun sa => (sa, c)) := by
    rw [Measure.map_map (by fun_prop) hψ]
    rfl
  rw [hL, map_stageK_reward (M := M) θ x, hR]
  have h :=
    map_compProd_comap_prod (ν := (M.stageK θ x).map (fun z => z.2)) (κ := M.rewardK)
      (f := (id : 𝒮 × 𝒜 → 𝒮 × 𝒜)) (g := fun _ => c) measurable_id measurable_const
  rw [Kernel.comap_id] at h
  apply Eq.trans _ h
  apply congrArg
    (fun f => Measure.map f ((M.stageK θ x).map (fun z => z.2) ⊗ₘ M.rewardK))
  funext p
  rfl

/--
A mixture of `stageK` still factors `((s, a), c, r)` through `rewardK`.
-/
private lemma map_bind_stageK_reward_prod
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜] [MeasurableSpace β]
  {M : Model Θ 𝒮 𝒜} [StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {ν : Measure 𝒮} [SFinite ν]
  {c : β}
-- given
  (θ : Θ) :
-- imply
  (M.stageK θ ∘ₘ ν).map (fun z : ℝ × 𝒮 × 𝒜 => ((z.2, c), z.1)) =
    (M.stageK θ ∘ₘ ν).map (fun z => (z.2, c)) ⊗ₘ
      M.rewardK.comap Prod.fst (by fun_prop) := by
-- proof
  have hΦ : Measurable fun z : ℝ × 𝒮 × 𝒜 => ((z.2, c), z.1) := by fun_prop
  have hg : Measurable fun z : ℝ × 𝒮 × 𝒜 => (z.2, c) := by fun_prop
  rw [Measure.map_comp _ _ hΦ, Measure.map_comp _ _ hg]
  ext s hs
  have hf :
    Measurable fun p =>
      (M.rewardK.comap Prod.fst (by fun_prop)) p (Prod.mk p ⁻¹' s) :=
    Kernel.measurable_kernel_prodMk_left hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), Measure.compProd_apply hs,
    lintegral_bind (Kernel.aemeasurable _) hf.aemeasurable]
  refine lintegral_congr fun x => ?_
  rw [Kernel.map_apply _ hΦ, Kernel.map_apply _ hg, ← Measure.compProd_apply hs]
  exact congrArg (fun μ => μ s) (map_stageK_reward_prod (M := M) (c := c) θ x)

/--
If a stage is drawn from `stageK` after a kernel `η` on some source, then `r` is
conditionally `rewardK` given `(s, a)`, independently of any measurable `g` of
the source.
-/
private lemma map_compProd_comp_stageK_reward
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜] [MeasurableSpace α] [MeasurableSpace β]
  {M : Model Θ 𝒮 𝒜} [StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {ν : Measure α} [SFinite ν]
  {η : Kernel α 𝒮} [IsSFiniteKernel η]
  {g : α → β} {hg : Measurable g}
-- given
  (θ : Θ) :
-- imply
  (ν ⊗ₘ (Kernel.comp (M.stageK θ) η)).map
    (fun p : α × (ℝ × 𝒮 × 𝒜) => ((p.2.2, g p.1), p.2.1)) =
    (ν ⊗ₘ (Kernel.comp (M.stageK θ) η)).map
      (fun p => (p.2.2, g p.1)) ⊗ₘ
        M.rewardK.comap Prod.fst (by fun_prop) := by
-- proof
  have hΦ : Measurable fun p : α × (ℝ × 𝒮 × 𝒜) => ((p.2.2, g p.1), p.2.1) := by fun_prop
  have hg' : Measurable fun p : α × (ℝ × 𝒮 × 𝒜) => (p.2.2, g p.1) := by fun_prop
  ext s hs
  have hL :
    ((ν ⊗ₘ (Kernel.comp (M.stageK θ) η)).map
        (fun p : α × (ℝ × 𝒮 × 𝒜) => ((p.2.2, g p.1), p.2.1))) s =
      ∫⁻ a, ((Kernel.comp (M.stageK θ) η) a).map (fun z => ((z.2, g a), z.1)) s ∂ν := by
    rw [Measure.map_apply hΦ hs, Measure.compProd_apply (hΦ hs)]
    refine lintegral_congr fun a => ?_
    rw [Measure.map_apply (by fun_prop) hs]
    rfl
  have hR :
    (((ν ⊗ₘ (Kernel.comp (M.stageK θ) η)).map (fun p => (p.2.2, g p.1))) ⊗ₘ
        M.rewardK.comap Prod.fst (by fun_prop)) s =
      ∫⁻ a, (((Kernel.comp (M.stageK θ) η) a).map (fun z => (z.2, g a)) ⊗ₘ
        M.rewardK.comap Prod.fst (by fun_prop)) s ∂ν := by
    have hρ :
      Measurable fun q =>
        (M.rewardK.comap Prod.fst (by fun_prop : Measurable Prod.fst)) q
          (Prod.mk q ⁻¹' s) :=
      Kernel.measurable_kernel_prodMk_left hs
    rw [Measure.compProd_apply hs, lintegral_map hρ hg']
    have hinterg' :
      Measurable fun p : α × (ℝ × 𝒮 × 𝒜) =>
        (M.rewardK.comap Prod.fst (by fun_prop)) (p.2.2, g p.1)
          (Prod.mk (p.2.2, g p.1) ⁻¹' s) :=
      hρ.comp hg'
    rw [Measure.lintegral_compProd hinterg']
    refine lintegral_congr fun a => ?_
    rw [Measure.compProd_apply hs, ← lintegral_map hρ
      (by fun_prop : Measurable fun z : ℝ × 𝒮 × 𝒜 => (z.2, g a))]
  rw [hL, hR]
  refine lintegral_congr fun a => ?_
  have h :=
    congrArg (fun μ => μ s)
      (map_bind_stageK_reward_prod (M := M) (ν := η a) (c := g a) θ)
  simpa [Kernel.comp_apply] using h

/--
Combine a `rewardK` factorization of `R` with an independent `transK`
factorization of the next state, after swapping the last two coordinates.
-/
private lemma map_compProd_reward_trans_swap
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜] [MeasurableSpace β]
  {M : Model Θ 𝒮 𝒜} [Model.HasMeasurableEnv M]
  {ξ : Measure (Prod (Prod 𝒮 𝒜) β)} [SFinite ξ] :
-- imply
  (ξ ⊗ₘ M.rewardK.comap Prod.fst (by fun_prop) ⊗ₘ
      M.transK.comap (fun p : Prod (Prod (Prod 𝒮 𝒜) β) ℝ => p.1.1) (by fun_prop)).map
      (fun q => (q.1.1, (q.2, q.1.2))) =
    ξ ⊗ₘ (M.transK ×ₖ M.rewardK).comap Prod.fst (by fun_prop) := by
-- proof
  have hΦ :
    Measurable fun q : Prod (Prod (Prod (Prod 𝒮 𝒜) β) ℝ) 𝒮 => (q.1.1, (q.2, q.1.2)) := by
    fun_prop
  ext s hs
  have hpre :
    MeasurableSet
      ((fun q : Prod (Prod (Prod (Prod 𝒮 𝒜) β) ℝ) 𝒮 => (q.1.1, (q.2, q.1.2))) ⁻¹' s) :=
    hΦ hs
  have hinterg :
    Measurable fun p =>
      (M.transK.comap (fun p : Prod (Prod (Prod 𝒮 𝒜) β) ℝ => p.1.1) (by fun_prop)) p
        (Prod.mk p ⁻¹'
          ((fun q : Prod (Prod (Prod (Prod 𝒮 𝒜) β) ℝ) 𝒮 => (q.1.1, (q.2, q.1.2))) ⁻¹' s)) :=
    Kernel.measurable_kernel_prodMk_left hpre
  rw [Measure.map_apply hΦ hs, Measure.compProd_apply hpre,
    Measure.lintegral_compProd hinterg, Measure.compProd_apply hs]
  refine lintegral_congr fun yz => ?_
  have hfun :
    (fun r =>
        (M.transK.comap (fun p : Prod (Prod (Prod 𝒮 𝒜) β) ℝ => p.1.1) (by fun_prop))
          (yz, r)
          (Prod.mk (yz, r) ⁻¹'
            ((fun q : Prod (Prod (Prod (Prod 𝒮 𝒜) β) ℝ) 𝒮 => (q.1.1, (q.2, q.1.2))) ⁻¹' s))) =
      fun r => M.transK yz.1 {x | (yz, (x, r)) ∈ s} := by
    funext r
    rw [Kernel.comap_apply]
    rfl
  have hrhs :
    ((M.transK ×ₖ M.rewardK).comap Prod.fst (by fun_prop)) yz (Prod.mk yz ⁻¹' s) =
      (M.transK ×ₖ M.rewardK) yz.1 {xr : 𝒮 × ℝ | (yz, xr) ∈ s} := by
    rw [Kernel.comap_apply]
    rfl
  rw [hfun, hrhs, Kernel.prod_apply]
  have hE : MeasurableSet {xr : 𝒮 × ℝ | (yz, xr) ∈ s} := measurable_prodMk_left hs
  have hF : MeasurableSet (Prod.swap ⁻¹' {xr : 𝒮 × ℝ | (yz, xr) ∈ s}) :=
    measurable_swap hE
  have hμr :
    (M.rewardK.comap Prod.fst (by fun_prop : Measurable Prod.fst)) yz =
      M.rewardK yz.1 := by
    ext t ht
    rw [Kernel.comap_apply]
  have hEswap :
    {xr : 𝒮 × ℝ | (yz, xr) ∈ s} =
      Prod.swap ⁻¹' (Prod.swap ⁻¹' {xr : 𝒮 × ℝ | (yz, xr) ∈ s}) :=
    rfl
  rw [hμr, hEswap, ← Measure.map_apply measurable_swap hF, Measure.prod_swap,
    Measure.prod_apply hF]
  rfl

/--
The law of `((s[t], a[t]), (s[:t], a[:t]), r[t])` factors through `rewardK`
given `(s[t], a[t])`.
-/
private lemma map_YZR
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {θ : Θ} {t : ℕ} :
-- imply
  (M θ).map
    (fun ω =>
      ((((ω t).2.1, (ω t).2.2),
          (fun i : Fin t => (ω i).2.1, fun i : Fin t => (ω i).2.2)),
        (ω t).1)) =
    (M θ).map
      (fun ω =>
        (((ω t).2.1, (ω t).2.2),
          (fun i : Fin t => (ω i).2.1, fun i : Fin t => (ω i).2.2))) ⊗ₘ
      M.rewardK.comap Prod.fst (by fun_prop) := by
-- proof
  cases t with
  | zero =>
    let μ := M θ
    let Z0 : (Fin 0 → 𝒮) × (Fin 0 → 𝒜) :=
      (fun i => Fin.elim0 i, fun i => Fin.elim0 i)
    have hZ : ∀ ω : ℕ → ℝ × 𝒮 × 𝒜,
        (fun i : Fin 0 => (ω i).2.1, fun i : Fin 0 => (ω i).2.2) = Z0 :=
      fun _ => by
        refine Prod.ext ?_ ?_
        ·
          funext i
          exact Fin.elim0 i
        ·
          funext i
          exact Fin.elim0 i
    have h0 := Map.eq.BindStageK.of.All_EqWithDensity (M := M) θ
    have hL :
      μ.map
        (fun ω =>
          ((((ω 0).2.1, (ω 0).2.2),
              (fun i : Fin 0 => (ω i).2.1, fun i : Fin 0 => (ω i).2.2)),
            (ω 0).1)) =
        (μ.map (fun ω => ω 0)).map (fun z => ((z.2, Z0), z.1)) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      apply congrArg (fun f => Measure.map f μ)
      funext ω
      simp [hZ ω]
    have hRμ :
      μ.map
        (fun ω =>
          (((ω 0).2.1, (ω 0).2.2),
            (fun i : Fin 0 => (ω i).2.1, fun i : Fin 0 => (ω i).2.2))) =
        (μ.map (fun ω => ω 0)).map (fun z => (z.2, Z0)) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      apply congrArg (fun f => Measure.map f μ)
      funext ω
      simp [hZ ω]
    rw [hL, hRμ, h0]
    exact map_bind_stageK_reward_prod (M := M) (c := Z0) θ
  | succ n =>
    let μ := M θ
    let μ₀ : Measure (ℝ × 𝒮 × 𝒜) := M.stageK θ ∘ₘ (M.init : Measure _)
    let H := Preorder.frestrictLe (π := fun _ : ℕ => ℝ × 𝒮 × 𝒜) n
    have hH : Measurable H := by fun_prop
    let e : (Π _ : Finset.Iic n, ℝ × 𝒮 × 𝒜) → ℝ × 𝒮 × 𝒜 :=
      fun hist => hist ⟨n, mem_Iic.2 le_rfl⟩
    have he : Measurable e := measurable_pi_apply _
    let Z_of :
      (Π _ : Finset.Iic n, ℝ × 𝒮 × 𝒜) → (Fin (n + 1) → 𝒮) × (Fin (n + 1) → 𝒜) :=
      fun hist =>
        (fun i : Fin (n + 1) => (hist ⟨i, mem_Iic.2 (Nat.lt_succ_iff.mp i.isLt)⟩).2.1,
          fun i : Fin (n + 1) => (hist ⟨i, mem_Iic.2 (Nat.lt_succ_iff.mp i.isLt)⟩).2.2)
    have hZof : Measurable Z_of := by fun_prop
    have hHX_stage :=
      Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
        (X := fun _ ↦ ℝ × 𝒮 × 𝒜) (μ₀ := μ₀) (κ := M.step θ) (a := n)
    have h1 : μ.map (fun ω => (H ω, ω (n + 1))) =
        μ.map H ⊗ₘ (M.K θ).comap e he := by
      unfold μ Model.traj
      rw [← hHX_stage]
      rfl
    have hK :
      (M.K θ).comap e he =
        Kernel.comp (M.stageK θ)
          ((M.transK.comap (fun z => z.2) (by fun_prop)).comap e he) := by
      unfold Model.K
      exact comp_comap he
    have h1' : μ.map (fun ω => (H ω, ω (n + 1))) =
        μ.map H ⊗ₘ
          (Kernel.comp (M.stageK θ)
            ((M.transK.comap (fun z => z.2) (by fun_prop)).comap e he)) := by
      rw [h1, hK]
    have hfac :=
      map_compProd_comp_stageK_reward (M := M) (ν := μ.map H)
        (η := (M.transK.comap (fun z => z.2) (by fun_prop)).comap e he)
        (g := Z_of) (hg := hZof) θ
    have hL :
      (μ.map (fun ω => (H ω, ω (n + 1)))).map
          (fun p => ((p.2.2, Z_of p.1), p.2.1)) =
        μ.map
          (fun ω =>
            ((((ω (n + 1)).2.1, (ω (n + 1)).2.2),
                (fun i : Fin (n + 1) => (ω i).2.1, fun i : Fin (n + 1) => (ω i).2.2)),
              (ω (n + 1)).1)) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      apply congrArg (fun f => Measure.map f μ)
      funext ω
      rfl
    have hRμ :
      (μ.map (fun ω => (H ω, ω (n + 1)))).map
          (fun p => (p.2.2, Z_of p.1)) =
        μ.map
          (fun ω =>
            (((ω (n + 1)).2.1, (ω (n + 1)).2.2),
              (fun i : Fin (n + 1) => (ω i).2.1, fun i : Fin (n + 1) => (ω i).2.2))) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      apply congrArg (fun f => Measure.map f μ)
      funext ω
      rfl
    rw [← h1'] at hfac
    rwa [hL, hRμ] at hfac

/--
The next state is drawn from `transK` given the current state-action history.
-/
private lemma map_HX
  [MeasurableSpace 𝒮] [ReferenceMeasure 𝒜]
  {M : Model Θ 𝒮 𝒜} [StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {θ : Θ} {t : ℕ} :
-- imply
  (M θ).map
    (fun ω =>
      (Preorder.frestrictLe (π := fun _ : ℕ => ℝ × 𝒮 × 𝒜) t ω,
        (ω (t + 1)).2.1)) =
    (M θ).map (Preorder.frestrictLe (π := fun _ : ℕ => ℝ × 𝒮 × 𝒜) t) ⊗ₘ
      M.transK.comap (fun hist => (hist ⟨t, mem_Iic.2 le_rfl⟩).2)
        (by fun_prop) := by
-- proof
  let μ := M θ
  let μ₀ : Measure (ℝ × 𝒮 × 𝒜) := M.stageK θ ∘ₘ (M.init : Measure _)
  let H := Preorder.frestrictLe (π := fun _ : ℕ => ℝ × 𝒮 × 𝒜) t
  let X : (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 := fun ω => (ω (t + 1)).2.1
  let e : (Π _ : Finset.Iic t, ℝ × 𝒮 × 𝒜) → ℝ × 𝒮 × 𝒜 :=
    fun hist => hist ⟨t, mem_Iic.2 le_rfl⟩
  have he : Measurable e := measurable_pi_apply _
  let Y_of : (Π _ : Finset.Iic t, ℝ × 𝒮 × 𝒜) → 𝒮 × 𝒜 := fun hist => (e hist).2
  have hYof : Measurable Y_of := measurable_snd.comp he
  have hHX_stage :=
    Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (X := fun _ ↦ ℝ × 𝒮 × 𝒜) (μ₀ := μ₀) (κ := M.step θ) (a := t)
  have h1 : μ.map (fun ω => (H ω, ω (t + 1))) =
      μ.map H ⊗ₘ (M.K θ).comap e he := by
    unfold μ Model.traj
    rw [← hHX_stage]
    rfl
  have h2 :=
    congrArg (Measure.map (Prod.map id (fun z : ℝ × 𝒮 × 𝒜 => z.2.1))) h1
  have hL :
    Measure.map (Prod.map id (fun z : ℝ × 𝒮 × 𝒜 => z.2.1))
      (μ.map (fun ω => (H ω, ω (t + 1)))) =
      μ.map (fun ω => (H ω, X ω)) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have hm : Measurable fun z : ℝ × 𝒮 × 𝒜 => z.2.1 := measurable_snd.fst
  have hmap :
    (μ.map H ⊗ₘ (M.K θ).comap e he).map
      (Prod.map id (fun z : ℝ × 𝒮 × 𝒜 => z.2.1)) =
    μ.map H ⊗ₘ ((M.K θ).map (fun z : ℝ × 𝒮 × 𝒜 => z.2.1)).comap e he := by
    rw [← Measure.compProd_map hm, ← Kernel.comap_map_comm _ he hm]
  apply Eq.trans hL.symm
  apply Eq.trans h2
  rw [hmap, map_K_state (M := M) θ]
  rw [← Kernel.comap_comp_right _ he measurable_snd]
  rfl

/--
Joint Markov property of the unified trajectory model `M θ`: the pair
`(s[t + 1], r[t])` is conditionally independent of the history
`(s[:t], a[:t])` given the current state and action `(s[t], a[t])`.
The next state is drawn from `trans (s[t], a[t])` and the current reward from
`reward (s[t], a[t])`, independently.
-/
@[path]
private lemma main
  [MeasurableSpace 𝒮] [StandardBorelSpace 𝒮] [Nonempty 𝒮]
  [ReferenceMeasure 𝒜] [StandardBorelSpace 𝒜] [Nonempty 𝒜]
  {M : Model Θ 𝒮 𝒜} [StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {r : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ → (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
  {θ : Θ}
  {t : ℕ}
-- given
  (h₀ : ∀ (t : ℕ), (· t) = (r[t], s[t], a[t])) :
-- imply
  let : ∀ (t : ℕ), Measurable (s[t], a[t]) :=
    fun t ↦ ((h₀ t) ▸ measurable_pi_apply t).snd
  (s[t + 1], r[t]) ⟂ᵢ[M θ] (s[:t], a[:t]) | (s[t], a[t]) := by
-- proof
  intro h
  obtain rfl : r = fun t ω ↦ (ω t).1 :=
    funext₂ fun t ω ↦
      (congrArg Prod.fst (congrFun (h₀ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 :=
    funext₂ fun t ω ↦
      (congrArg (·.2.1) (congrFun (h₀ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 :=
    funext₂ fun t ω ↦
      (congrArg (·.2.2) (congrFun (h₀ t) ω)).symm
  let μ := M θ
  let H := Preorder.frestrictLe (π := fun _ : ℕ => ℝ × 𝒮 × 𝒜) t
  let Y : (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 × 𝒜 := fun ω => ((ω t).2.1, (ω t).2.2)
  let Z : (ℕ → ℝ × 𝒮 × 𝒜) → (Fin t → 𝒮) × (Fin t → 𝒜) :=
    fun ω => (fun i => (ω i).2.1, fun i => (ω i).2.2)
  let X : (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮 := fun ω => (ω (t + 1)).2.1
  let R : (ℕ → ℝ × 𝒮 × 𝒜) → ℝ := fun ω => (ω t).1
  have hH : Measurable H := by fun_prop
  have hY : Measurable Y := by fun_prop
  have hZ : Measurable Z := by fun_prop
  have hX : Measurable X := by fun_prop
  have hR : Measurable R := by fun_prop
  have hXR : Measurable fun ω => (X ω, R ω) := hX.prodMk hR
  let e : (Π _ : Finset.Iic t, ℝ × 𝒮 × 𝒜) → ℝ × 𝒮 × 𝒜 :=
    fun hist => hist ⟨t, mem_Iic.2 le_rfl⟩
  have he : Measurable e := measurable_pi_apply _
  let Y_of : (Π _ : Finset.Iic t, ℝ × 𝒮 × 𝒜) → 𝒮 × 𝒜 := fun hist => (e hist).2
  have hYof : Measurable Y_of := measurable_snd.comp he
  let Z_of : (Π _ : Finset.Iic t, ℝ × 𝒮 × 𝒜) → (Fin t → 𝒮) × (Fin t → 𝒜) :=
    fun hist =>
      (fun i : Fin t => (hist ⟨i, mem_Iic.2 (Nat.le_of_lt i.isLt)⟩).2.1,
        fun i : Fin t => (hist ⟨i, mem_Iic.2 (Nat.le_of_lt i.isLt)⟩).2.2)
  have hZof : Measurable Z_of := by fun_prop
  let R_of : (Π _ : Finset.Iic t, ℝ × 𝒮 × 𝒜) → ℝ := fun hist => (e hist).1
  have hRof : Measurable R_of := measurable_fst.comp he
  let φ : (Π _ : Finset.Iic t, ℝ × 𝒮 × 𝒜) → Prod (Prod (Prod 𝒮 𝒜) ((Fin t → 𝒮) × (Fin t → 𝒜))) ℝ :=
    fun hist => ((Y_of hist, Z_of hist), R_of hist)
  have hφ : Measurable φ := by fun_prop
  have hHX := map_HX (M := M) (θ := θ) (t := t)
  have hYZR := map_YZR (M := M) (θ := θ) (t := t)
  have hY_of_φ : Y_of = (fun p : Prod (Prod (Prod 𝒮 𝒜) ((Fin t → 𝒮) × (Fin t → 𝒜))) ℝ => p.1.1) ∘ φ :=
    rfl
  have hpush :
    (μ.map H ⊗ₘ M.transK.comap Y_of hYof).map (Prod.map φ id) =
      (μ.map H).map φ ⊗ₘ
        M.transK.comap
          (fun p : Prod (Prod (Prod 𝒮 𝒜) ((Fin t → 𝒮) × (Fin t → 𝒜))) ℝ => p.1.1)
          (by fun_prop) := by
    have hfst :
      Measurable
        fun p : Prod (Prod (Prod 𝒮 𝒜) ((Fin t → 𝒮) × (Fin t → 𝒜))) ℝ => p.1.1 :=
      by fun_prop
    have hcomap :
      M.transK.comap Y_of hYof =
        (M.transK.comap
            (fun p : Prod (Prod (Prod 𝒮 𝒜) ((Fin t → 𝒮) × (Fin t → 𝒜))) ℝ => p.1.1)
            (by fun_prop)).comap φ hφ := by
      exact (Kernel.comap_comp_right M.transK hφ hfst).symm
    rw [hcomap]
    exact MapComap_MapId.eq.Map.of.Measurable hφ
  have hφH :
    (μ.map H).map φ = μ.map (fun ω => ((Y ω, Z ω), R ω)) := by
    rw [Measure.map_map hφ hH]
    rfl
  have hmid :
    (μ.map H ⊗ₘ M.transK.comap Y_of hYof).map (Prod.map φ id) =
      (μ.map (fun ω => ((Y ω, Z ω), R ω))) ⊗ₘ
        M.transK.comap
          (fun p : Prod (Prod (Prod 𝒮 𝒜) ((Fin t → 𝒮) × (Fin t → 𝒜))) ℝ => p.1.1)
          (by fun_prop) := by
    rw [hpush, hφH]
  have hmid' :
    (μ.map H ⊗ₘ M.transK.comap Y_of hYof).map (Prod.map φ id) =
      μ.map (fun ω => (Y ω, Z ω)) ⊗ₘ M.rewardK.comap Prod.fst (by fun_prop) ⊗ₘ
        M.transK.comap
          (fun p : Prod (Prod (Prod 𝒮 𝒜) ((Fin t → 𝒮) × (Fin t → 𝒜))) ℝ => p.1.1)
          (by fun_prop) := by
    rw [hmid, hYZR]
  have hjoint :
    μ.map (fun ω => ((Y ω, Z ω), (X ω, R ω))) =
      μ.map (fun ω => (Y ω, Z ω)) ⊗ₘ
        (M.transK ×ₖ M.rewardK).comap Prod.fst (by fun_prop) := by
    have hswap :=
      map_compProd_reward_trans_swap (M := M)
        (ξ := μ.map (fun ω => (Y ω, Z ω)))
    have h2 :
      (μ.map (fun ω => (Y ω, Z ω)) ⊗ₘ M.rewardK.comap Prod.fst (by fun_prop) ⊗ₘ
          M.transK.comap
            (fun p : Prod (Prod (Prod 𝒮 𝒜) ((Fin t → 𝒮) × (Fin t → 𝒜))) ℝ => p.1.1)
            (by fun_prop)).map
          (fun q => (q.1.1, (q.2, q.1.2))) =
        μ.map (fun ω => (Y ω, Z ω)) ⊗ₘ
          (M.transK ×ₖ M.rewardK).comap Prod.fst (by fun_prop) :=
      hswap
    have h3 :
      ((μ.map H ⊗ₘ M.transK.comap Y_of hYof).map (Prod.map φ id)).map
        (fun q => (q.1.1, (q.2, q.1.2))) =
        μ.map (fun ω => ((Y ω, Z ω), (X ω, R ω))) := by
      have hmeas1 :
        Measurable
          fun q : Prod (Prod (Prod (Prod 𝒮 𝒜) ((Fin t → 𝒮) × (Fin t → 𝒜))) ℝ) 𝒮 =>
            (q.1.1, (q.2, q.1.2)) := by
        fun_prop
      have hmeas2 :
        Measurable
          (Prod.map φ (id : 𝒮 → 𝒮)) :=
        hφ.prodMap measurable_id
      have hmeas3 : Measurable fun ω => (H ω, X ω) := by fun_prop
      have hmeas4 :
        Measurable
          fun p : (Π _ : Finset.Iic t, ℝ × 𝒮 × 𝒜) × 𝒮 =>
            ((φ p.1).1, (p.2, (φ p.1).2)) := by
        fun_prop
      rw [Measure.map_map hmeas1 hmeas2]
      have hcomp :
        (fun q : Prod (Prod (Prod (Prod 𝒮 𝒜) ((Fin t → 𝒮) × (Fin t → 𝒜))) ℝ) 𝒮 =>
            (q.1.1, (q.2, q.1.2))) ∘
          Prod.map φ (id : 𝒮 → 𝒮) =
          fun p : (Π _ : Finset.Iic t, ℝ × 𝒮 × 𝒜) × 𝒮 =>
            ((φ p.1).1, (p.2, (φ p.1).2)) :=
        rfl
      rw [hcomp, ← hHX, Measure.map_map hmeas4 hmeas3]
      rfl
    apply Eq.trans h3.symm
    rwa [hmid']
  have hYX :
    μ.map (fun ω => (Y ω, (X ω, R ω))) =
      μ.map Y ⊗ₘ (M.transK ×ₖ M.rewardK) := by
    have hmap := congrArg (Measure.map (Prod.map Prod.fst id)) hjoint
    have hL :
      Measure.map (Prod.map Prod.fst id)
        (μ.map (fun ω => ((Y ω, Z ω), (X ω, R ω)))) =
        μ.map (fun ω => (Y ω, (X ω, R ω))) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    apply Eq.trans hL.symm
    apply Eq.trans hmap
    rw [MapComap_MapId.eq.Map.of.Measurable (by fun_prop)]
    rw [Measure.map_map measurable_fst (by fun_prop)]
    rfl
  have hcd_YZ :
    condDistrib (fun ω => (X ω, R ω)) (fun ω => (Y ω, Z ω)) μ =ᵐ[μ.map (fun ω => (Y ω, Z ω))]
      (M.transK ×ₖ M.rewardK).comap Prod.fst (by fun_prop) :=
    condDistrib_ae_eq_of_measure_eq_compProd (by fun_prop) hXR.aemeasurable hjoint
  have hcd_Y :
    condDistrib (fun ω => (X ω, R ω)) Y μ =ᵐ[μ.map Y] (M.transK ×ₖ M.rewardK) :=
    condDistrib_ae_eq_of_measure_eq_compProd (by fun_prop) hXR.aemeasurable hYX
  apply CondIndepFun.symm
  dsimp only [JointRandomSymbol, Function.getSlice, getElem]
  change Z ⟂ᵢ[Y, hY; μ] (fun ω => (X ω, R ω))
  rw [condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight hXR hZ hY]
  refine hcd_YZ.trans ?_
  change
    (fun p => (M.transK ×ₖ M.rewardK) p.1) =ᵐ[μ.map (fun ω => (Y ω, Z ω))]
      (fun p => condDistrib (fun ω => (X ω, R ω)) Y μ p.1)
  apply ae_eq_comp measurable_fst.aemeasurable
  convert hcd_Y.symm
  rw [Measure.map_map measurable_fst (hY.prodMk hZ)]
  apply congrArg (fun f => Measure.map f μ)
  ext1
  rfl


-- created on 2026-11-18
