import sympy.stats.policy_trajectory
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Markov-chain API for the policy-gradient trajectory model

Facts about `PolicyGradient.Model` (see `sympy.stats.policy_trajectory`) used by the RL lemmas
(`Tensor.*.Bellman*`, `Tensor.EqExpect.of.Eq_Expect.V_Function`, …):

* stage laws: `ω 0 ∼ μ₀`, `ω (t+1) ∼ K ∘ law(ω t)`, `ω t ∼ stageK ∘ law(s t)`;
* the Markov property along histories (`hist_step`, `hist_mul`, `hist_iter`) with the iterated
  kernel `Kf` and the time-independent `W`;
* closed forms of the joint probabilities and conditional expectations used by `V` and `Q`
  (`real_sa`, `E_s_r`, `E_xu_r0`, `E_xu_r`, `E_s_h`, `E_xu_h`, `V_eq`, `Q_eq`, `v_closed`);
* boundedness and summability of the discounted conditional reward series.

No `Lemma.*` module is imported here.
-/
open MeasureTheory ProbabilityTheory Finset

namespace PolicyGradient

namespace Model

variable {Θ S A : Type*} [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]

theorem compProd_comap_map {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (ν : Measure α) [SFinite ν] (κ : Kernel β γ) [IsSFiniteKernel κ] {f : α → β} (hf : Measurable f) :
    (ν ⊗ₘ κ.comap f hf).map (Prod.map f id) = (ν.map f) ⊗ₘ κ := by
  ext s hs
  rw [Measure.map_apply (hf.prodMap measurable_id) hs, Measure.compProd_apply (hf.prodMap measurable_id hs),
    Measure.compProd_apply hs, lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  rfl

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem joint_succ (M : Model Θ S A) (θ : Θ) (t : ℕ) :
    (M.traj θ).map (fun ω => (ω t, ω (t + 1))) = ((M.traj θ).map (fun ω => ω t)) ⊗ₘ M.K θ := by
  have h := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ ↦ Step S A) (μ₀ := M.μ₀ θ) (κ := M.step θ) (a := t)
  let e : (Π _ : Iic t, Step S A) → Step S A := fun h ↦ h ⟨t, mem_Iic.2 le_rfl⟩
  have he : Measurable e := measurable_pi_apply _
  have h₂ := congrArg (Measure.map (Prod.map e id)) h
  rw [Measure.map_map (he.prodMap measurable_id) (by fun_prop)] at h₂
  have h₃ : M.step θ t = (M.K θ).comap e he := rfl
  rw [h₃, compProd_comap_map _ _ he, Measure.map_map he (by fun_prop)] at h₂
  exact h₂.symm

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem stage_zero (M : Model Θ S A) (θ : Θ) :
    (M.traj θ).map (fun ω => ω 0) = M.μ₀ θ := by
  unfold Model.traj Kernel.trajMeasure
  rw [Measure.map_comp _ _ (measurable_pi_apply 0)]
  have h₁ : (Kernel.traj (X := fun _ ↦ Step S A) (M.step θ) 0).map (fun ω => ω 0)
      = ((Kernel.traj (X := fun _ ↦ Step S A) (M.step θ) 0).map (Preorder.frestrictLe 0)).map
          (fun h => h ⟨0, mem_Iic.2 le_rfl⟩) := by
    rw [← Kernel.map_comp_right _ (by fun_prop) (by fun_prop)]
    rfl
  rw [h₁, Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Kernel.id_map (by fun_prop),
    Measure.deterministic_comp_eq_map, Measure.map_map (by fun_prop) (by fun_prop)]
  have h₂ : ((fun h : (Π _ : Iic 0, Step S A) => h ⟨0, mem_Iic.2 le_rfl⟩) ∘
      ⇑(MeasurableEquiv.piUnique (fun i : Iic 0 => (fun _ => Step S A) i)).symm) = id := by
    funext x; rfl
  rw [h₂, Measure.map_id]

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem stage_succ (M : Model Θ S A) (θ : Θ) (t : ℕ) :
    (M.traj θ).map (fun ω => ω (t + 1)) = M.K θ ∘ₘ (M.traj θ).map (fun ω => ω t) := by
  have h := congrArg (Measure.map Prod.snd) (joint_succ M θ t)
  rw [Measure.map_map measurable_snd (by fun_prop)] at h
  have h₂ := Measure.snd_compProd ((M.traj θ).map (fun ω => ω t)) (M.K θ)
  rw [Measure.snd] at h₂
  rw [← h₂, ← h]
  rfl

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem fst_stageK_comp (M : Model Θ S A) (θ : Θ) (ν : Measure S) :
    (M.stageK θ ∘ₘ ν).map Prod.fst = ν := by
  have := M.env.reward_markov
  rw [Measure.map_comp _ _ measurable_fst]
  have h : (M.stageK θ).map Prod.fst = Kernel.deterministic id measurable_id := by
    unfold Model.stageK
    rw [← Kernel.fst_eq]
    exact Kernel.fst_prod (Kernel.deterministic (id : S → S) measurable_id) (M.pol.kernel θ ⊗ₖ M.env.reward)
  rw [h, Measure.deterministic_comp_eq_map, Measure.map_id]

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem stage_law (M : Model Θ S A) (θ : Θ) (t : ℕ) :
    (M.traj θ).map (fun ω => ω t) = M.stageK θ ∘ₘ (M.traj θ).map (s t) := by
  have h₀ : (M.traj θ).map (s t) = ((M.traj θ).map (fun ω => ω t)).map Prod.fst := by
    rw [Measure.map_map measurable_fst (measurable_pi_apply t)]; rfl
  rw [h₀]
  cases t with
  | zero =>
    rw [stage_zero, Model.μ₀, fst_stageK_comp]
  | succ t =>
    rw [stage_succ, Model.K, ← Measure.comp_assoc, fst_stageK_comp]

theorem integral_comp_bdd {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) [IsProbabilityMeasure μ] (κ : Kernel α β) [IsMarkovKernel κ]
    {f : β → E} (hf : StronglyMeasurable f) {C : ℝ} (hC : ∀ b, ‖f b‖ ≤ C) :
    ∫ b, f b ∂(κ ∘ₘ μ) = ∫ a, ∫ b, f b ∂(κ a) ∂μ := by
  rw [← Measure.snd_compProd μ κ, Measure.snd, integral_map measurable_snd.aemeasurable
    hf.aestronglyMeasurable]
  rw [Measure.integral_compProd]
  exact Integrable.of_bound (hf.comp_measurable measurable_snd).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun p => hC p.2)

omit [DecidableEq S] [DecidableEq A] in
theorem integral_stageK (M : Model Θ S A) (θ : Θ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : Step S A → E} (hf : StronglyMeasurable f) {C : ℝ}
    (hC : ∀ z, ‖f z‖ ≤ C) (y : S) :
    ∫ z, f z ∂(M.stageK θ y) = ∑ u, M.pol.prob θ y u • ∫ ρ, f (y, u, ρ) ∂(M.env.reward (y, u)) := by
  have := M.env.reward_markov
  unfold Model.stageK
  rw [Kernel.prod_apply, Kernel.deterministic_apply]
  rw [id, Measure.dirac_prod, integral_map (by fun_prop) hf.aestronglyMeasurable]
  rw [ProbabilityTheory.integral_compProd (f := fun x : A × ℝ => f (y, x))
    (Integrable.of_bound (hf.comp_measurable (by fun_prop)).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun p => hC _))]
  rw [integral_fintype (Integrable.of_bound (by
      exact (StronglyMeasurable.of_discrete).aestronglyMeasurable) C
      (Filter.Eventually.of_forall fun u => by
        calc _ ≤ ∫ ρ, ‖f (y, u, ρ)‖ ∂(M.env.reward (y, u)) := norm_integral_le_integral_norm _
          _ ≤ ∫ ρ, C ∂(M.env.reward (y, u)) := by
            apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
              (integrable_const C) (Filter.Eventually.of_forall fun ρ => hC _)
          _ = C := by simp))]
  congr 1
  funext u
  congr 1
  show ((M.pol.measure θ y) {u}).toReal = _
  rw [Policy.measure]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply,
    Measure.dirac_apply' _ (measurableSet_singleton u), smul_eq_mul]
  rw [Finset.sum_eq_single u (fun b _ hb => by simp [hb]) (by simp)]
  simp [M.pol.nonneg θ y u]

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem Kf_bdd (M : Model Θ S A) (θ : Θ) {f : Step S A → ℝ} (hf : StronglyMeasurable f) {C : ℝ}
    (hC : ∀ z, ‖f z‖ ≤ C) (j : ℕ) :
    StronglyMeasurable (M.Kf θ f j) ∧ ∀ z, ‖M.Kf θ f j z‖ ≤ C := by
  induction j with
  | zero => exact ⟨hf, hC⟩
  | succ j ih =>
    refine ⟨?_, fun z => ?_⟩
    · show StronglyMeasurable (fun z => ∫ w, M.Kf θ f j w ∂(M.K θ z))
      exact (ih.1.comp_measurable measurable_snd).integral_kernel_prod_right' (κ := M.K θ)
    · have h := norm_integral_le_of_norm_le_const (μ := M.K θ z) (Filter.Eventually.of_forall ih.2)
      show ‖∫ w, M.Kf θ f j w ∂(M.K θ z)‖ ≤ C
      simpa using h

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem hist_step (M : Model Θ S A) (θ : Θ) (n : ℕ)
    {φ : (Π _ : Iic n, Step S A) × Step S A → ℝ} (hφ : StronglyMeasurable φ) {C : ℝ}
    (hC : ∀ p, ‖φ p‖ ≤ C) :
    ∫ ω, φ (Preorder.frestrictLe n ω, ω (n + 1)) ∂(M.traj θ) =
      ∫ h, ∫ z, φ (h, z) ∂(M.K θ (h ⟨n, mem_Iic.2 le_rfl⟩))
        ∂((M.traj θ).map (Preorder.frestrictLe n)) := by
  have h := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ ↦ Step S A) (μ₀ := M.μ₀ θ) (κ := M.step θ) (a := n)
  have e : ∫ ω, φ (Preorder.frestrictLe n ω, ω (n + 1)) ∂(M.traj θ) =
      ∫ p, φ p ∂((M.traj θ).map (fun x ↦ (Preorder.frestrictLe n x, x (n + 1)))) := by
    rw [integral_map (by fun_prop) hφ.aestronglyMeasurable]
  rw [e]
  unfold Model.traj
  rw [← h, Measure.integral_compProd]
  · rfl
  · exact Integrable.of_bound hφ.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem hist_mul (M : Model Θ S A) (θ : Θ) (n : ℕ) {G : (Π _ : Iic n, Step S A) → ℝ}
    (hG : StronglyMeasurable G) {CG : ℝ} (hCG : ∀ h, ‖G h‖ ≤ CG)
    {g : Step S A → ℝ} (hg : StronglyMeasurable g) {C : ℝ} (hC : ∀ z, ‖g z‖ ≤ C) :
    ∫ ω, G (Preorder.frestrictLe n ω) * g (ω (n + 1)) ∂(M.traj θ) =
      ∫ ω, G (Preorder.frestrictLe n ω) * ∫ z, g z ∂(M.K θ (ω n)) ∂(M.traj θ) := by
  rw [hist_step M θ n (φ := fun p => G p.1 * g p.2)
    ((hG.comp_measurable measurable_fst).mul (hg.comp_measurable measurable_snd)) (C := CG * C)
    (fun p => by
      rw [norm_mul]
      exact mul_le_mul (hCG _) (hC _) (norm_nonneg _) ((norm_nonneg _).trans (hCG p.1)))]
  simp_rw [integral_const_mul]
  have hm : StronglyMeasurable (fun h : (Π _ : Iic n, Step S A) =>
      G h * ∫ z, g z ∂(M.K θ (h ⟨n, mem_Iic.2 le_rfl⟩))) := by
    refine hG.mul ?_
    exact (hg.comp_measurable measurable_snd).integral_kernel_prod_right' (κ := M.step θ n)
  rw [integral_map (by fun_prop) hm.aestronglyMeasurable]
  rfl

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem hist_iter (M : Model Θ S A) (θ : Θ) {f : Step S A → ℝ} (hf : StronglyMeasurable f) {C : ℝ}
    (hC : ∀ z, ‖f z‖ ≤ C) (j : ℕ) :
    ∀ n {G : (Π _ : Iic n, Step S A) → ℝ}, StronglyMeasurable G → ∀ {CG : ℝ}, (∀ h, ‖G h‖ ≤ CG) →
      ∫ ω, G (Preorder.frestrictLe n ω) * f (ω (n + j)) ∂(M.traj θ) =
        ∫ ω, G (Preorder.frestrictLe n ω) * M.Kf θ f j (ω n) ∂(M.traj θ) := by
  induction j with
  | zero => intro n G _ _ _; rfl
  | succ j ih =>
    intro n G hG CG hCG
    have h₁ := ih (n + 1) (G := G ∘ Preorder.frestrictLe₂ (π := fun _ : ℕ => Step S A) (by omega : n ≤ n + 1))
      (hG.comp_measurable (Preorder.measurable_frestrictLe₂ _)) (CG := CG) (fun _ => hCG _)
    have e : n + (j + 1) = n + 1 + j := by omega
    rw [e]
    exact h₁.trans (hist_mul M θ n hG hCG (Kf_bdd M θ hf hC j).1 (Kf_bdd M θ hf hC j).2)

omit [MeasurableSingletonClass
  S] [Fintype S] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A] in
theorem s_meas (t : ℕ) : Measurable (s (S := S) (A := A) t) :=
  measurable_fst.comp (measurable_pi_apply t)

omit [MeasurableSingletonClass
  S] [Fintype S] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A] in
theorem a_meas (t : ℕ) : Measurable (a (S := S) (A := A) t) :=
  measurable_fst.comp (measurable_snd.comp (measurable_pi_apply t))

theorem disc_sm {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
    (φ : α → ℝ) : StronglyMeasurable φ := StronglyMeasurable.of_discrete

theorem ite_mul_bdd {α : Type*} (p : α → Prop) [DecidablePred p] {g : α → ℝ} {C : ℝ}
    (hC : ∀ z, ‖g z‖ ≤ C) (z : α) : ‖(if p z then (1:ℝ) else 0) * g z‖ ≤ C := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (by split_ifs <;> simp)).trans (hC z)

omit [MeasurableSingletonClass
  S] [Fintype S] [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem rc_bdd (M : Model Θ S A) (z : Step S A) : ‖M.rc z‖ ≤ |M.env.R| := by
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨le_trans (neg_le_neg (le_abs_self _)) (le_max_left _ _),
    max_le (neg_le_abs _) ((min_le_left _ _).trans (le_abs_self _))⟩

omit [MeasurableSingletonClass
  S] [Fintype S] [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem rc_sm (M : Model Θ S A) : StronglyMeasurable M.rc :=
  (Measurable.max measurable_const (Measurable.min measurable_const measurable_snd.snd)).stronglyMeasurable

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem stageK_null (M : Model Θ S A) (θ : Θ) (y : S) :
    M.stageK θ y {z | z.2.2 ∉ Set.Icc (-M.env.R) M.env.R} = 0 := by
  have hs : MeasurableSet {z : Step S A | z.2.2 ∉ Set.Icc (-M.env.R) M.env.R} :=
    (measurableSet_Icc.compl).preimage measurable_snd.snd
  have := M.env.reward_markov
  unfold Model.stageK
  rw [Kernel.prod_apply, Kernel.deterministic_apply, id, Measure.dirac_prod,
    Measure.map_apply measurable_prodMk_left hs, Kernel.compProd_apply (measurable_prodMk_left hs)]
  have h : ∀ b, M.env.reward (y, b) (Prod.mk b ⁻¹' (Prod.mk y ⁻¹'
      {z : Step S A | z.2.2 ∉ Set.Icc (-M.env.R) M.env.R})) = 0 := fun b => M.env.reward_bdd (y, b)
  simp only [h, lintegral_zero]

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem r_ae (M : Model Θ S A) (θ : Θ) (t : ℕ) : ∀ᵐ ω ∂(M.traj θ), r t ω = M.rc (ω t) := by
  have hs : MeasurableSet {z : Step S A | z.2.2 ∉ Set.Icc (-M.env.R) M.env.R} :=
    (measurableSet_Icc.compl).preimage measurable_snd.snd
  have h : (M.traj θ).map (fun ω => ω t) {z | z.2.2 ∉ Set.Icc (-M.env.R) M.env.R} = 0 := by
    rw [stage_law, Measure.bind_apply hs (Kernel.aemeasurable _)]
    exact (lintegral_congr (fun y => stageK_null M θ y)).trans lintegral_zero
  rw [Measure.map_apply (measurable_pi_apply t) hs] at h
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) h
  simp only [Set.mem_ofPred_eq] at hω ⊢
  intro hI
  apply hω
  simp only [Model.rc, r]
  rw [min_eq_right hI.2, max_eq_right hI.1]

omit [DecidableEq A] in
theorem split_inner (M : Model Θ S A) (θ : Θ) {g : Step S A → ℝ} (hg : StronglyMeasurable g) {C : ℝ}
    (hC : ∀ z, ‖g z‖ ≤ C) (y y' : S) :
    ∫ z, (if z.1 = y then (1:ℝ) else 0) * g z ∂(M.stageK θ y') =
      (if y' = y then 1 else 0) * ∫ z, g z ∂(M.stageK θ y') := by
  have hm : StronglyMeasurable (fun z : Step S A => (if z.1 = y then (1:ℝ) else 0) * g z) :=
    ((disc_sm (fun x : S => if x = y then (1:ℝ) else 0)).comp_measurable measurable_fst).mul hg
  rw [integral_stageK M θ hm (ite_mul_bdd (fun z : Step S A => z.1 = y) hC), integral_stageK M θ hg hC]
  by_cases h : y' = y <;> simp [h]

omit [DecidableEq A] in
theorem stage_split (M : Model Θ S A) (θ : Θ) (t : ℕ) {g : Step S A → ℝ} (hg : StronglyMeasurable g)
    {C : ℝ} (hC : ∀ z, ‖g z‖ ≤ C) (x : S) :
    ∫ ω, (if s t ω = x then (1:ℝ) else 0) * g (ω t) ∂(M.traj θ) =
      (M.traj θ).real (s t ⁻¹' {x}) * ∫ z, g z ∂(M.stageK θ x) := by
  have hm : StronglyMeasurable (fun z : Step S A => (if z.1 = x then (1:ℝ) else 0) * g z) :=
    ((disc_sm (fun y : S => if y = x then (1:ℝ) else 0)).comp_measurable measurable_fst).mul hg
  have : IsProbabilityMeasure ((M.traj θ).map (s t)) :=
    Measure.isProbabilityMeasure_map (s_meas t).aemeasurable
  have e1 : ∫ ω, (if s t ω = x then (1:ℝ) else 0) * g (ω t) ∂(M.traj θ) =
      ∫ z, (if z.1 = x then (1:ℝ) else 0) * g z ∂((M.traj θ).map (fun ω => ω t)) := by
    rw [integral_map (measurable_pi_apply t).aemeasurable hm.aestronglyMeasurable]; rfl
  rw [e1, stage_law, integral_comp_bdd _ _ hm (ite_mul_bdd (fun z : Step S A => z.1 = x) hC)]
  simp_rw [split_inner M θ hg hC x]
  have h₂ : ∀ y', (if y' = x then (1:ℝ) else 0) * ∫ z, g z ∂(M.stageK θ y') =
      (if y' = x then 1 else 0) * ∫ z, g z ∂(M.stageK θ x) := by
    intro y'; by_cases h : y' = x <;> simp [h]
  simp_rw [h₂]
  rw [integral_mul_const]
  congr 1
  have h₃ : (fun y' : S => if y' = x then (1:ℝ) else 0) = ({x} : Set S).indicator 1 := by
    funext y'; simp [Set.indicator_apply]
  rw [h₃, integral_indicator_one (measurableSet_singleton x), measureReal_def, measureReal_def,
    Measure.map_apply (s_meas t) (measurableSet_singleton x)]

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem Kf_succ (M : Model Θ S A) (θ : Θ) {f : Step S A → ℝ} (hf : StronglyMeasurable f) {C : ℝ}
    (hC : ∀ z, ‖f z‖ ≤ C) (j : ℕ) (z : Step S A) :
    M.Kf θ f (j + 1) z = ∑ y, M.T z.1 z.2.1 y * M.W θ f j y := by
  have := M.env.trans_markov
  show ∫ w, M.Kf θ f j w ∂(M.K θ z) = _
  have hK : M.K θ z = M.stageK θ ∘ₘ M.env.trans (z.1, z.2.1) := by
    rw [Model.K, Kernel.comp_apply, Kernel.comap_apply]
  rw [hK, integral_comp_bdd _ _ (Kf_bdd M θ hf hC j).1 (Kf_bdd M θ hf hC j).2,
    integral_fintype Integrable.of_finite]
  rfl

omit [DecidableEq S] [DecidableEq A] in
theorem W_succ (M : Model Θ S A) (θ : Θ) {f : Step S A → ℝ} (hf : StronglyMeasurable f) {C : ℝ}
    (hC : ∀ z, ‖f z‖ ≤ C) (j : ℕ) (x : S) :
    M.W θ f (j + 1) x = ∑ u, M.pol.prob θ x u * ∑ y, M.T x u y * M.W θ f j y := by
  have := M.env.reward_markov
  have h := Kf_bdd M θ hf hC (j + 1)
  unfold Model.W
  rw [integral_stageK M θ h.1 h.2]
  simp_rw [Kf_succ M θ hf hC j]
  simp [smul_eq_mul]
  rfl

omit [DecidableEq S] [DecidableEq A] in
theorem W_zero (M : Model Θ S A) (θ : Θ) {f : Step S A → ℝ} (hf : StronglyMeasurable f) {C : ℝ}
    (hC : ∀ z, ‖f z‖ ≤ C) (x : S) :
    M.W θ f 0 x = ∑ u, M.pol.prob θ x u * ∫ ρ, f (x, u, ρ) ∂(M.env.reward (x, u)) := by
  show ∫ z, f z ∂(M.stageK θ x) = _
  rw [integral_stageK M θ hf hC]
  rfl

omit [MeasurableSingletonClass A] [Fintype A] [DecidableEq A] in
theorem ind_fst_sm (x : S) : StronglyMeasurable (fun z : Step S A => if z.1 = x then (1:ℝ) else 0) :=
  (disc_sm (fun y : S => if y = x then (1:ℝ) else 0)).comp_measurable measurable_fst

omit [MeasurableSingletonClass S] [Fintype S] [DecidableEq S] in
theorem ind_snd_sm (u : A) : StronglyMeasurable (fun z : Step S A => if z.2.1 = u then (1:ℝ) else 0) :=
  (disc_sm (fun v : A => if v = u then (1:ℝ) else 0)).comp_measurable measurable_snd.fst

theorem ind_bdd {α : Type*} (p : α → Prop) [DecidablePred p] (z : α) :
    ‖(if p z then (1:ℝ) else 0)‖ ≤ 1 := by
  split_ifs <;> simp

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem stage_iter (M : Model Θ S A) (θ : Θ) {f : Step S A → ℝ} (hf : StronglyMeasurable f) {C : ℝ}
    (hC : ∀ z, ‖f z‖ ≤ C) (t j : ℕ) {G : Step S A → ℝ} (hG : StronglyMeasurable G) {CG : ℝ}
    (hCG : ∀ z, ‖G z‖ ≤ CG) :
    ∫ ω, G (ω t) * f (ω (t + j)) ∂(M.traj θ) = ∫ ω, G (ω t) * M.Kf θ f j (ω t) ∂(M.traj θ) :=
  hist_iter M θ hf hC j t (G := fun h => G (h ⟨t, mem_Iic.2 le_rfl⟩))
    (hG.comp_measurable (measurable_pi_apply _)) (CG := CG) (fun _ => hCG _)

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem cond_int (M : Model Θ S A) (θ : Θ) {B : Set (ℕ → Step S A)} (hB : MeasurableSet B)
    (f : (ℕ → Step S A) → ℝ) :
    ∫ ω, f ω ∂(M.traj θ)[|B] = ((M.traj θ).real B)⁻¹ * ∫ ω, B.indicator 1 ω * f ω ∂(M.traj θ) := by
  rw [ProbabilityTheory.cond, integral_smul_measure, ← integral_indicator hB, ENNReal.toReal_inv,
    ← measureReal_def, smul_eq_mul]
  congr 1
  congr 1
  funext ω
  by_cases h : ω ∈ B <;> simp [h]

omit [DecidableEq A] in
theorem E_s_r (M : Model Θ S A) (θ : Θ) (t j : ℕ) (x : S) :
    ∫ ω, (if s t ω = x then (1:ℝ) else 0) * r (t + j) ω ∂(M.traj θ) =
      (M.traj θ).real (s t ⁻¹' {x}) * M.W θ M.rc j x := by
  have h₁ : ∫ ω, (if s t ω = x then (1:ℝ) else 0) * r (t + j) ω ∂(M.traj θ) =
      ∫ ω, (if s t ω = x then (1:ℝ) else 0) * M.rc (ω (t + j)) ∂(M.traj θ) :=
    integral_congr_ae ((r_ae M θ (t + j)).mono fun ω h => by dsimp only; rw [h])
  have hK := Kf_bdd M θ (rc_sm M) (rc_bdd M) j
  rw [h₁]
  exact (stage_iter M θ (rc_sm M) (rc_bdd M) t j (ind_fst_sm x) (ind_bdd _)).trans
    (stage_split M θ t hK.1 hK.2 x)

omit [DecidableEq S] in
theorem stageK_ind_snd (M : Model Θ S A) (θ : Θ) {g : Step S A → ℝ} (hg : StronglyMeasurable g)
    {C : ℝ} (hC : ∀ z, ‖g z‖ ≤ C) (x : S) (u : A) :
    ∫ z, (if z.2.1 = u then (1:ℝ) else 0) * g z ∂(M.stageK θ x) =
      M.pol.prob θ x u * ∫ ρ, g (x, u, ρ) ∂(M.env.reward (x, u)) := by
  rw [integral_stageK M θ (f := fun z => (if z.2.1 = u then (1:ℝ) else 0) * g z)
    ((ind_snd_sm u).mul hg) (ite_mul_bdd (fun z : Step S A => z.2.1 = u) hC)]
  rw [Finset.sum_eq_single u (fun b _ hb => by simp [hb]) (by simp)]
  simp [smul_eq_mul]

theorem P_xu (M : Model Θ S A) (θ : Θ) (t : ℕ) (x : S) (u : A) :
    ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) ∂(M.traj θ) =
      (M.traj θ).real (s t ⁻¹' {x}) * M.pol.prob θ x u := by
  have := M.env.reward_markov
  have h₁ : ∀ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) =
      (if s t ω = x then (1:ℝ) else 0) * (fun z : Step S A => if z.2.1 = u then (1:ℝ) else 0) (ω t) := by
    intro ω; simp only [s, a]
    by_cases h1 : (ω t).1 = x <;> by_cases h2 : (ω t).2.1 = u <;> simp [h1, h2]
  simp_rw [h₁]
  rw [stage_split M θ t (ind_snd_sm u) (ind_bdd _) x]
  have h₂ := stageK_ind_snd M θ (g := fun _ => (1:ℝ)) stronglyMeasurable_const (C := 1) (by simp) x u
  simp only [mul_one, integral_const, probReal_univ, smul_eq_mul] at h₂
  rw [h₂]

theorem E_xu_r0 (M : Model Θ S A) (θ : Θ) (t : ℕ) (x : S) (u : A) :
    ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * r t ω ∂(M.traj θ) =
      (M.traj θ).real (s t ⁻¹' {x}) * M.pol.prob θ x u * ∫ ρ, M.rc (x, u, ρ) ∂(M.env.reward (x, u)) := by
  have h₀ : ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * r t ω ∂(M.traj θ) =
      ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * M.rc (ω t) ∂(M.traj θ) :=
    integral_congr_ae ((r_ae M θ t).mono fun ω h => by dsimp only; rw [h])
  have h₁ : ∀ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * M.rc (ω t) =
      (if s t ω = x then (1:ℝ) else 0) *
        (fun z : Step S A => (if z.2.1 = u then (1:ℝ) else 0) * M.rc z) (ω t) := by
    intro ω; simp only [s, a]
    by_cases h1 : (ω t).1 = x <;> by_cases h2 : (ω t).2.1 = u <;> simp [h1, h2]
  rw [h₀]
  simp_rw [h₁]
  rw [stage_split M θ t (g := fun z => (if z.2.1 = u then (1:ℝ) else 0) * M.rc z) ((ind_snd_sm u).mul (rc_sm M)) (ite_mul_bdd (fun z : Step S A => z.2.1 = u) (rc_bdd M)) x,
    stageK_ind_snd M θ (rc_sm M) (rc_bdd M) x u, mul_assoc]

theorem ind_xu_sm (x : S) (u : A) :
    StronglyMeasurable (fun z : Step S A => if z.1 = x ∧ z.2.1 = u then (1:ℝ) else 0) :=
  (disc_sm (fun p : S × A => if p.1 = x ∧ p.2 = u then (1:ℝ) else 0)).comp_measurable
    (measurable_fst.prodMk measurable_snd.fst)

theorem E_xu_const (M : Model Θ S A) (θ : Θ) (t : ℕ) (x : S) (u : A) (φ : S → A → ℝ) :
    ∫ ω, (if (ω t).1 = x ∧ (ω t).2.1 = u then (1:ℝ) else 0) * φ (ω t).1 (ω t).2.1 ∂(M.traj θ) =
      (M.traj θ).real (s t ⁻¹' {x}) * M.pol.prob θ x u * φ x u := by
  have h₁ : ∀ ω : ℕ → Step S A, (if (ω t).1 = x ∧ (ω t).2.1 = u then (1:ℝ) else 0) * φ (ω t).1 (ω t).2.1 =
      (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * φ x u := by
    intro ω; simp only [s, a]
    by_cases h1 : (ω t).1 = x <;> by_cases h2 : (ω t).2.1 = u <;> simp [h1, h2]
  simp_rw [h₁]
  rw [integral_mul_const, P_xu]

theorem E_xu_r (M : Model Θ S A) (θ : Θ) (t j : ℕ) (x : S) (u : A) :
    ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * r (t + (j + 1)) ω ∂(M.traj θ) =
      (M.traj θ).real (s t ⁻¹' {x}) * M.pol.prob θ x u * ∑ y, M.T x u y * M.W θ M.rc j y := by
  have h₀ : ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * r (t + (j + 1)) ω ∂(M.traj θ) =
      ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * M.rc (ω (t + (j + 1))) ∂(M.traj θ) :=
    integral_congr_ae ((r_ae M θ (t + (j + 1))).mono fun ω h => by dsimp only; rw [h])
  rw [h₀]
  refine (stage_iter M θ (rc_sm M) (rc_bdd M) t (j + 1) (ind_xu_sm x u) (ind_bdd _)).trans ?_
  simp_rw [Kf_succ M θ (rc_sm M) (rc_bdd M) j]
  exact E_xu_const M θ t x u (fun x' u' => ∑ y, M.T x' u' y * M.W θ M.rc j y)

omit [MeasurableSpace S] [MeasurableSingletonClass S] [DecidableEq S] in
theorem h_bdd (h : S → ℝ) (y : S) : ‖h y‖ ≤ ∑ y', ‖h y'‖ :=
  Finset.single_le_sum (f := fun y' => ‖h y'‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ y)

omit [DecidableEq S] [DecidableEq A] in
theorem W_fst_zero (M : Model Θ S A) (θ : Θ) (h : S → ℝ) (y : S) :
    M.W θ (fun z => h z.1) 0 y = h y := by
  have := M.env.reward_markov
  rw [W_zero M θ (f := fun z => h z.1) ((disc_sm h).comp_measurable measurable_fst) (fun z => h_bdd h z.1)]
  simp [← Finset.sum_mul, M.pol.sum_eq_one]

theorem E_xu_h (M : Model Θ S A) (θ : Θ) (t : ℕ) (x : S) (u : A) (h : S → ℝ) :
    ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * h (s (t + 1) ω) ∂(M.traj θ) =
      (M.traj θ).real (s t ⁻¹' {x}) * M.pol.prob θ x u * ∑ y, M.T x u y * h y := by
  have hf : StronglyMeasurable (fun z : Step S A => h z.1) := (disc_sm h).comp_measurable measurable_fst
  refine (stage_iter M θ hf (fun z => h_bdd h z.1) t 1 (ind_xu_sm x u) (ind_bdd _)).trans ?_
  simp_rw [Kf_succ M θ hf (fun z => h_bdd h z.1) 0, W_fst_zero]
  exact E_xu_const M θ t x u (fun x' u' => ∑ y, M.T x' u' y * h y)

omit [DecidableEq A] in
theorem E_s_h (M : Model Θ S A) (θ : Θ) (t : ℕ) (x : S) (h : S → ℝ) :
    ∫ ω, (if s t ω = x then (1:ℝ) else 0) * h (s (t + 1) ω) ∂(M.traj θ) =
      (M.traj θ).real (s t ⁻¹' {x}) * ∑ u, M.pol.prob θ x u * ∑ y, M.T x u y * h y := by
  have hf : StronglyMeasurable (fun z : Step S A => h z.1) := (disc_sm h).comp_measurable measurable_fst
  have hK := Kf_bdd M θ hf (fun z => h_bdd h z.1) 1
  refine (stage_iter M θ hf (fun z => h_bdd h z.1) t 1 (ind_fst_sm x) (ind_bdd _)).trans ?_
  refine (stage_split M θ t hK.1 hK.2 x).trans ?_
  congr 1
  show M.W θ (fun z => h z.1) (0 + 1) x = _
  rw [W_succ M θ hf (fun z => h_bdd h z.1) 0]
  simp_rw [W_fst_zero]

omit [MeasurableSingletonClass A] [DecidableEq A] in
theorem cond_s (M : Model Θ S A) (θ : Θ) (t : ℕ) (x : S) (f : (ℕ → Step S A) → ℝ) :
    ∫ ω, f ω ∂(M.traj θ)[|s t ⁻¹' {x}] =
      ((M.traj θ).real (s t ⁻¹' {x}))⁻¹ * ∫ ω, (if s t ω = x then (1:ℝ) else 0) * f ω ∂(M.traj θ) := by
  rw [cond_int M θ (s_meas t (measurableSet_singleton x))]
  congr 2
  funext ω
  by_cases h : s t ω = x <;> simp [h]

theorem real_sa (M : Model Θ S A) (θ : Θ) (t : ℕ) (x : S) (u : A) :
    (M.traj θ).real (s t ⁻¹' {x} ∩ a t ⁻¹' {u}) = (M.traj θ).real (s t ⁻¹' {x}) * M.pol.prob θ x u := by
  rw [← P_xu M θ t x u, ← integral_indicator_one
    ((s_meas t (measurableSet_singleton x)).inter (a_meas t (measurableSet_singleton u)))]
  congr 1
  funext ω
  by_cases h1 : s t ω = x <;> by_cases h2 : a t ω = u <;> simp [h1, h2]

theorem cond_sa (M : Model Θ S A) (θ : Θ) (t : ℕ) (x : S) (u : A) (f : (ℕ → Step S A) → ℝ) :
    ∫ ω, f ω ∂(M.traj θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}] =
      ((M.traj θ).real (s t ⁻¹' {x}) * M.pol.prob θ x u)⁻¹ *
        ∫ ω, (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * f ω ∂(M.traj θ) := by
  rw [cond_int M θ ((s_meas t (measurableSet_singleton x)).inter (a_meas t (measurableSet_singleton u))),
    real_sa]
  congr 2
  funext ω
  by_cases h1 : s t ω = x <;> by_cases h2 : a t ω = u <;> simp [h1, h2]

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem W_bdd (M : Model Θ S A) (θ : Θ) (j : ℕ) (y : S) : ‖M.W θ M.rc j y‖ ≤ |M.env.R| := by
  have h := norm_integral_le_of_norm_le_const (μ := M.stageK θ y)
    (Filter.Eventually.of_forall (Kf_bdd M θ (rc_sm M) (rc_bdd M) j).2)
  show ‖∫ z, M.Kf θ M.rc j z ∂(M.stageK θ y)‖ ≤ _
  simpa using h

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem summable_W (M : Model Θ S A) (θ : Θ) {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1) (y : S) :
    Summable (fun k => γ ^ k * M.W θ M.rc k y) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hγ.1 hγ.2).mul_right |M.env.R|) ?_
  intro k
  rw [norm_mul, norm_pow, Real.norm_of_nonneg hγ.1]
  exact mul_le_mul_of_nonneg_left (W_bdd M θ k y) (pow_nonneg hγ.1 k)

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem cond_r_bdd (M : Model Θ S A) (θ : Θ) (B : Set (ℕ → Step S A)) (t : ℕ) :
    ‖∫ ω, r t ω ∂(M.traj θ)[|B]‖ ≤ |M.env.R| := by
  have hae : ∀ᵐ ω ∂(M.traj θ)[|B], ‖r t ω‖ ≤ |M.env.R| :=
    cond_absolutelyContinuous.ae_le ((r_ae M θ t).mono fun ω h => by rw [h]; exact rc_bdd M _)
  by_cases hB : M.traj θ B = 0
  · rw [cond_eq_zero_of_meas_eq_zero hB]; simp
  · have := cond_isProbabilityMeasure (μ := M.traj θ) hB
    have h := norm_integral_le_of_norm_le_const hae
    simpa using h

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem summable_cond (M : Model Θ S A) (θ : Θ) {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1)
    (B : Set (ℕ → Step S A)) (t : ℕ) :
    Summable (fun k => γ ^ k * ∫ ω, r (t + k) ω ∂(M.traj θ)[|B]) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hγ.1 hγ.2).mul_right |M.env.R|) ?_
  intro k
  rw [norm_mul, norm_pow, Real.norm_of_nonneg hγ.1]
  exact mul_le_mul_of_nonneg_left (cond_r_bdd M θ B (t + k)) (pow_nonneg hγ.1 k)

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem meas_zero_of_real (M : Model Θ S A) (θ : Θ) {B : Set (ℕ → Step S A)}
    (h : (M.traj θ).real B = 0) : M.traj θ B = 0 :=
  (measureReal_eq_zero_iff (measure_ne_top _ _)).1 h

omit [MeasurableSingletonClass
  S] [Fintype S] [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem T_nonneg (M : Model Θ S A) (x : S) (u : A) (y : S) : 0 ≤ M.T x u y := by
  unfold Model.T; exact measureReal_nonneg

theorem tsum_pull {ι : Type*} [Fintype ι] {γ : ℝ} (c : ι → ℝ) (w : ι → ℕ → ℝ)
    (hw : ∀ i, Summable (fun k => γ ^ k * w i k)) :
    ∑' k, γ ^ k * ∑ i, c i * w i k = ∑ i, c i * ∑' k, γ ^ k * w i k := by
  simp_rw [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun i _ => ((hw i).mul_left (c i)).congr (fun k => by ring))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← tsum_mul_left]
  congr 1; funext k; ring

theorem summable_pull {ι : Type*} [Fintype ι] {γ : ℝ} (c : ι → ℝ) (w : ι → ℕ → ℝ)
    (hw : ∀ i, Summable (fun k => γ ^ k * w i k)) :
    Summable (fun k => γ ^ k * ∑ i, c i * w i k) := by
  simp_rw [Finset.mul_sum]
  exact summable_sum (fun i _ => ((hw i).mul_left (c i)).congr (fun k => by ring))

omit [DecidableEq A] in
theorem V_eq (M : Model Θ S A) (θ : Θ) (γ : ℝ) (t : ℕ) (x : S)
    (hP : (M.traj θ).real (s t ⁻¹' {x}) ≠ 0) :
    M.V θ γ t x = ∑' k, γ ^ k * M.W θ M.rc k x := by
  unfold Model.V
  congr 1; funext k
  rw [cond_s, E_s_r, inv_mul_cancel_left₀ hP]

theorem Q_eq (M : Model Θ S A) (θ : Θ) {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1) (t : ℕ) (x : S) (u : A)
    (hP : (M.traj θ).real (s t ⁻¹' {x}) * M.pol.prob θ x u ≠ 0) :
    M.Q θ γ t x u = (∫ ρ, M.rc (x, u, ρ) ∂(M.env.reward (x, u))) +
      γ * ∑ y, M.T x u y * ∑' k, γ ^ k * M.W θ M.rc k y := by
  unfold Model.Q
  rw [(summable_cond M θ hγ _ t).tsum_eq_zero_add]
  have h0 : ∫ ω, r (t + 0) ω ∂(M.traj θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}] =
      ∫ ρ, M.rc (x, u, ρ) ∂(M.env.reward (x, u)) := by
    rw [cond_sa, add_zero, E_xu_r0, inv_mul_cancel_left₀ hP]
  have hk : ∀ k, ∫ ω, r (t + (k + 1)) ω ∂(M.traj θ)[|s t ⁻¹' {x} ∩ a t ⁻¹' {u}] =
      ∑ y, M.T x u y * M.W θ M.rc k y := by
    intro k; rw [cond_sa, E_xu_r, inv_mul_cancel_left₀ hP]
  rw [h0, pow_zero, one_mul]
  simp_rw [hk, pow_succ, mul_comm _ γ, mul_assoc γ]
  rw [tsum_mul_left, tsum_pull _ _ (fun y => summable_W M θ hγ y)]

omit [DecidableEq S] [DecidableEq A] in
theorem v_closed (M : Model Θ S A) (θ : Θ) {γ : ℝ} (hγ : γ ∈ Set.Ico 0 1) (x : S) :
    ∑' k, γ ^ k * M.W θ M.rc k x = M.W θ M.rc 0 x +
      γ * ∑ u, M.pol.prob θ x u * ∑ y, M.T x u y * ∑' k, γ ^ k * M.W θ M.rc k y := by
  rw [(summable_W M θ hγ x).tsum_eq_zero_add, pow_zero, one_mul]
  congr 1
  simp_rw [W_succ M θ (rc_sm M) (rc_bdd M), pow_succ, mul_comm _ γ, mul_assoc γ]
  rw [tsum_mul_left, tsum_pull _ _ (fun u => summable_pull _ _ (fun y => summable_W M θ hγ y))]
  congr 1
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [tsum_pull _ _ (fun y => summable_W M θ hγ y)]

theorem integrable_ind_sa (M : Model Θ S A) (θ : Θ) (t : ℕ) (x : S) (u : A) (c : ℝ) :
    Integrable (fun ω => (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * c) (M.traj θ) := by
  refine Integrable.of_bound (C := ‖c‖) ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · exact (((disc_sm (fun p : S × A => if p.1 = x ∧ p.2 = u then (1:ℝ) else 0)).comp_measurable
      ((s_meas t).prodMk (a_meas t))).mul stronglyMeasurable_const).aestronglyMeasurable
  · rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (by split_ifs <;> simp)

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem integrable_ind_h {B : Type*} [MeasurableSpace B] [MeasurableSingletonClass B] [Fintype B]
    (M : Model Θ S A) (θ : Θ) (X : (ℕ → Step S A) → B) (hX : Measurable X) (φ : B → ℝ) :
    Integrable (fun ω => φ (X ω)) (M.traj θ) := by
  refine Integrable.of_bound (C := ∑ b, ‖φ b‖) ((disc_sm φ).comp_measurable hX).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  exact Finset.single_le_sum (f := fun b => ‖φ b‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ _)

omit [MeasurableSingletonClass A] [DecidableEq S] [DecidableEq A] in
theorem integrable_ind_r (M : Model Θ S A) (θ : Θ) {B : Type*} [MeasurableSpace B]
    [MeasurableSingletonClass B] [Fintype B] (X : (ℕ → Step S A) → B) (hX : Measurable X)
    (φ : B → ℝ) (t : ℕ) :
    Integrable (fun ω => φ (X ω) * r t ω) (M.traj θ) := by
  refine Integrable.of_bound (C := (∑ b, ‖φ b‖) * |M.env.R|) ?_ ((r_ae M θ t).mono fun ω h => ?_)
  · exact (((disc_sm φ).comp_measurable hX).mul
      (measurable_snd.snd.comp (measurable_pi_apply t)).stronglyMeasurable).aestronglyMeasurable
  · rw [norm_mul, h]
    exact mul_le_mul (Finset.single_le_sum (f := fun b => ‖φ b‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ _)) (rc_bdd M _) (norm_nonneg _)
      (Finset.sum_nonneg (fun _ _ => norm_nonneg _))

omit [DecidableEq A] in
theorem reach (M : Model Θ S A) (θ : Θ) (t : ℕ) (x : S) (u : A) (y : S)
    (hP : (M.traj θ).real (s t ⁻¹' {x}) ≠ 0) (hz : M.pol.prob θ x u * M.T x u y ≠ 0) :
    (M.traj θ).real (s (t + 1) ⁻¹' {y}) ≠ 0 := by
  have hE : ∫ ω, (if s t ω = x then (1:ℝ) else 0) * (if s (t + 1) ω = y then (1:ℝ) else 0) ∂(M.traj θ) =
      (M.traj θ).real (s t ⁻¹' {x}) * ∑ u', M.pol.prob θ x u' * M.T x u' y := by
    refine (E_s_h M θ t x (fun y' => if y' = y then (1:ℝ) else 0)).trans ?_
    congr 1
    refine Finset.sum_congr rfl (fun u' _ => ?_)
    congr 1
    simp
  have hpos : 0 < (M.traj θ).real (s t ⁻¹' {x}) * ∑ u', M.pol.prob θ x u' * M.T x u' y := by
    refine mul_pos (lt_of_le_of_ne measureReal_nonneg (Ne.symm hP)) ?_
    refine lt_of_lt_of_le (lt_of_le_of_ne (mul_nonneg (M.pol.nonneg θ x u) (T_nonneg M x u y))
      (Ne.symm hz)) ?_
    exact Finset.single_le_sum (f := fun u' => M.pol.prob θ x u' * M.T x u' y)
      (fun u' _ => mul_nonneg (M.pol.nonneg _ _ _) (T_nonneg M _ _ _)) (Finset.mem_univ u)
  have hle : ∫ ω, (if s t ω = x then (1:ℝ) else 0) * (if s (t + 1) ω = y then (1:ℝ) else 0)
      ∂(M.traj θ) ≤ (M.traj θ).real (s (t + 1) ⁻¹' {y}) := by
    rw [← integral_indicator_one (s_meas (t + 1) (measurableSet_singleton y))]
    refine integral_mono
      (integrable_ind_h M θ (fun ω => (s t ω, s (t + 1) ω)) ((s_meas t).prodMk (s_meas (t + 1)))
        (fun p => (if p.1 = x then (1:ℝ) else 0) * (if p.2 = y then (1:ℝ) else 0)))
      ((integrable_const (1:ℝ)).indicator (s_meas (t + 1) (measurableSet_singleton y))) (fun ω => ?_)
    by_cases h1 : s t ω = x <;> by_cases h2 : s (t + 1) ω = y <;> simp [h1, h2]
  intro h0
  rw [h0, hE] at hle
  linarith

theorem alg1 {c γ Y Z : ℝ} (hc : c ≠ 0) : c⁻¹ * (γ * (c * Y) + c * Z) = Z + γ * Y := by
  rw [mul_add, mul_left_comm γ, inv_mul_cancel_left₀ hc, inv_mul_cancel_left₀ hc, add_comm]

omit [DecidableEq A] in
theorem V_succ_eq (M : Model Θ S A) (θ : Θ) (γ : ℝ) (t : ℕ) (x : S) (u : A)
    (hP : (M.traj θ).real (s t ⁻¹' {x}) ≠ 0) (y : S) :
    M.pol.prob θ x u * (M.T x u y * M.V θ γ (t + 1) y) =
      M.pol.prob θ x u * (M.T x u y * ∑' k, γ ^ k * M.W θ M.rc k y) := by
  by_cases hz : M.pol.prob θ x u * M.T x u y = 0
  · rw [← mul_assoc, ← mul_assoc, hz, zero_mul, zero_mul]
  · rw [V_eq M θ γ (t + 1) y (reach M θ t x u y hP hz)]

end Model

end PolicyGradient
