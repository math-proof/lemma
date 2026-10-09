import sympy.stats.policy_trajectory
import sympy.stats.hidden_markov_sequence
import Lemma.Random.Integral_Mul.eq.Integral_Mul_Integral.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable
import Lemma.Random.Integral_MulEq12.eq.MulEqIntegral.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.Integral.eq.Integral_Integral.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.Integral_MulEqS.eq.MulRealPreimageSIntegral.of.All_LeNorm.StronglyMeasurable
import Lemma.Random.MEqCondExp_Integral.of.Integrable.Measurable
import Lemma.Random.AeNe_0
import Lemma.Real.LeNorm_Mul1.of.All_LeNorm
import Lemma.Real.Norm_1.le.One
import Lemma.Real.StronglyMeasurable.discrete
import Lemma.Real.StronglyMeasurable_Eq12
open MeasureTheory ProbabilityTheory PolicyGradient Random Real


/--
History irrelevance (one-step Markov property) of the trajectory model `M θ`: given the current state `s n`,
the next step `(a n, r n, s (n + 1))` (action, reward and next state) is conditionally independent of the
history `(r, s, a)[:n]`. It is built into the Ionescu-Tulcea construction of `M θ`: `Model.step` only reads
the last stage, the action and reward are drawn from `M.stageK θ (s n)` and the next state from
`M.env.trans (s n, a n)`. This is the hypothesis `h₁` of `Random.CondIndep.of.All_CondIndep.All_MeasurableJoint`.
Proof: the state `s n` is discrete, so it suffices that, for measurable `E` and `H`,
`Pr(s n = y, (a n, r n, s (n + 1)) ∈ E, (r, s, a)[:n] ∈ H) = Pr(s n = y, (r, s, a)[:n] ∈ H) * c(y, E)`;
summing over the next state `s (n + 1) = y'` this follows from the one-step kernel identities
`Random.Integral_Mul.eq.Integral_Mul_Integral.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable`.
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
  {θ : Θ}
  {n : ℕ}
-- given
  (h₁ : ∀ t, (· t) = (r t, s t, a t)) :
-- imply
  let h : ∀ t, Measurable (r t, s t, a t) := fun t ↦ (h₁ t) ▸ measurable_pi_apply t;
  (a n, r n, s (n + 1)) ⟂ᵢ[M θ] (r, s, a)[:n] | s n := by
-- proof
  intro h
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  classical
  have := M.env.trans_markov
  have hT1 : ∀ x u y, ‖M.T x u y‖ ≤ 1 := fun x u y ↦ by
    show ‖(M.env.trans (x, u)).real {y}‖ ≤ 1
    rw [Real.norm_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  have hTm : ∀ y, Measurable (fun w : ℝ × S × A ↦ M.T w.2.1 w.2.2 y) := fun y ↦
    (measurable_of_countable (fun p : S × A ↦ M.T p.1 p.2 y)).comp (measurable_snd.fst.prodMk measurable_snd.snd)
  have hι : ∀ {β : Type _} [MeasurableSpace β] {p : β → Prop}, MeasurableSet {b | p b} →
      StronglyMeasurable (fun b ↦ if p b then (1 : ℝ) else 0) := fun hp ↦
    (Measurable.ite hp measurable_const measurable_const).stronglyMeasurable
  -- the kernel step: `𝔼[1{s[n+1] = y} * f(ω[n+1]) | ω[n] = w] = T(w, y) * 𝔼[f | stageK y]`
  have hstep : ∀ (y : S) (w : ℝ × S × A) {f : ℝ × S × A → ℝ} {C : ℝ}, StronglyMeasurable f → (∀ z, ‖f z‖ ≤ C) →
      ∫ z, (if z.2.1 = y then (1 : ℝ) else 0) * f z ∂(M.K θ w) = M.T w.2.1 w.2.2 y * ∫ z, f z ∂(M.stageK θ y) := by
    intro y w f C hf hC
    have hK : M.K θ w = M.stageK θ ∘ₘ M.env.trans (w.2.1, w.2.2) := by
      rw [Model.K, Kernel.comp_apply, Kernel.comap_apply]
    rw [hK, Integral.eq.Integral_Integral.of.All_LeNorm.StronglyMeasurable (f := fun z : ℝ × S × A ↦ (if z.2.1 = y then (1 : ℝ) else 0) * f z)
      (((StronglyMeasurable.discrete (fun x : S ↦ if x = y then (1 : ℝ) else 0)).comp_measurable
        measurable_snd.fst).mul hf) (LeNorm_Mul1.of.All_LeNorm (p := (fun z : ℝ × S × A ↦ z.2.1 = y)) hC),
      integral_fintype Integrable.of_finite]
    simp_rw [Integral_MulEq12.eq.MulEqIntegral.of.All_LeNorm.StronglyMeasurable (M := M) hf hC θ y]
    rw [Finset.sum_eq_single y (fun b _ hb ↦ by simp [hb]) (by simp)]
    simp only [if_true, one_mul, smul_eq_mul]
    rfl
  have hstep1 : ∀ (y : S) (w : ℝ × S × A), ∫ z, (if z.2.1 = y then (1 : ℝ) else 0) ∂(M.K θ w) = M.T w.2.1 w.2.2 y := by
    intro y w
    have h := hstep y w (f := fun _ ↦ (1 : ℝ)) stronglyMeasurable_const (fun _ ↦ le_of_eq norm_one)
    simp only [mul_one, integral_const, probReal_univ, smul_eq_mul] at h
    exact h
  -- given the history `ω[:k]` and `s[k] = y`, the stage `ω[k]` is drawn from `stageK y`
  have hC : ∀ k y (H : Set (Fin k → ℝ × S × A)), MeasurableSet H → ∀ {f : ℝ × S × A → ℝ} {C : ℝ}, StronglyMeasurable f → (∀ z, ‖f z‖ ≤ C) →
      ∫ ω, (if (fun i : Fin k ↦ ω i) ∈ H then (1 : ℝ) else 0) * ((if (ω k).2.1 = y then (1 : ℝ) else 0) * f (ω k)) ∂(M θ) =
        (∫ ω, (if (fun i : Fin k ↦ ω i) ∈ H then (1 : ℝ) else 0) * (if (ω k).2.1 = y then (1 : ℝ) else 0) ∂(M θ)) * ∫ z, f z ∂(M.stageK θ y) := by
    intro k y H hH f C hf hCf
    cases k with
    | zero =>
      have h1 : ∫ ω, (if (ω 0).2.1 = y then (1 : ℝ) else 0) * f (ω 0) ∂(M θ) = (M θ).real ((fun ω ↦ (ω 0).2.1) ⁻¹' {y}) * ∫ z, f z ∂(M.stageK θ y) :=
        Integral_MulEqS.eq.MulRealPreimageSIntegral.of.All_LeNorm.StronglyMeasurable (M := M) h₁ hf hCf θ 0 y
      have h2 : ∫ ω, (if (ω 0).2.1 = y then (1 : ℝ) else 0) * 1 ∂(M θ) = (M θ).real ((fun ω ↦ (ω 0).2.1) ⁻¹' {y}) * ∫ z, (1 : ℝ) ∂(M.stageK θ y) :=
        Integral_MulEqS.eq.MulRealPreimageSIntegral.of.All_LeNorm.StronglyMeasurable (M := M) h₁ (g := fun _ ↦ (1 : ℝ)) stronglyMeasurable_const (fun _ ↦ le_of_eq norm_one) θ 0 y
      simp only [mul_one, integral_const, probReal_univ, smul_eq_mul] at h2
      if hH0 : (Fin.elim0 : Fin 0 → ℝ × S × A) ∈ H then
        have e : ∀ ω : ℕ → ℝ × S × A, (if (fun i : Fin 0 ↦ ω i) ∈ H then (1 : ℝ) else 0) = 1 := fun ω ↦
          if_pos (by rwa [Subsingleton.elim (fun i : Fin 0 ↦ ω i) Fin.elim0])
        simp only [e, one_mul]
        rw [h1, h2]
      else
        have e : ∀ ω : ℕ → ℝ × S × A, (if (fun i : Fin 0 ↦ ω i) ∈ H then (1 : ℝ) else 0) = 0 := fun ω ↦
          if_neg (by rwa [Subsingleton.elim (fun i : Fin 0 ↦ ω i) Fin.elim0])
        simp only [e, zero_mul, integral_zero]
    | succ m =>
      let G : (Π _ : Finset.Iic m, ℝ × S × A) → ℝ := fun h ↦
        if (fun i : Fin (m + 1) ↦ h ⟨i, Finset.mem_Iic.2 (Nat.lt_succ_iff.1 i.2)⟩) ∈ H then 1 else 0
      have hGm : StronglyMeasurable G := hι ((Measurable.of_eval fun i ↦ measurable_pi_apply _) hH)
      have hCG : ∀ h, ‖G h‖ ≤ 1 := fun h ↦ Norm_1.le.One _
      have h1 := Integral_Mul.eq.Integral_Mul_Integral.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable (M := M) hGm hCG
        (g := fun z ↦ (if z.2.1 = y then (1 : ℝ) else 0) * f z) ((StronglyMeasurable_Eq12 y).mul hf) (LeNorm_Mul1.of.All_LeNorm hCf) θ
      have h2 := Integral_Mul.eq.Integral_Mul_Integral.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable (M := M) hGm hCG
        (g := fun z ↦ if z.2.1 = y then (1 : ℝ) else 0) (StronglyMeasurable_Eq12 y) (fun _ ↦ Norm_1.le.One _) θ
      simp only [hstep y _ hf hCf] at h1
      simp only [hstep1] at h2
      calc _ = ∫ ω, G (Preorder.frestrictLe m ω) * ((if (ω (m + 1)).2.1 = y then (1 : ℝ) else 0) * f (ω (m + 1))) ∂(M θ) := rfl
        _ = (∫ ω, G (Preorder.frestrictLe m ω) * M.T (ω m).2.1 (ω m).2.2 y ∂(M θ)) * ∫ z, f z ∂(M.stageK θ y) := by
          rw [h1, ← integral_mul_const]
          simp_rw [mul_assoc]
        _ = _ := by
          rw [← h2]
          rfl
  have hHm : Measurable (fun ω : ℕ → ℝ × S × A ↦ fun i : Fin n ↦ ω i) := Measurable.of_eval fun i ↦ measurable_pi_apply _
  have hsm : Measurable (fun ω : ℕ → ℝ × S × A ↦ (ω n).2.1) := (measurable_pi_apply n).snd.fst
  have hXm : Measurable (fun ω : ℕ → ℝ × S × A ↦ ((ω n).2.2, (ω n).1, (ω (n + 1)).2.1)) :=
    (measurable_pi_apply n).snd.snd.prodMk ((measurable_pi_apply n).fst.prodMk (measurable_pi_apply (n + 1)).snd.fst)
  -- `φ w = Pr((a, r, s') ∈ E)` for the action and reward of the stage `w` and the next state `s' ∼ T(w)`
  have hK : ∀ y (E : Set (A × ℝ × S)) (H : Set (Fin n → ℝ × S × A)), MeasurableSet E → MeasurableSet H →
      (M θ).real ((fun ω ↦ (ω n).2.1) ⁻¹' {y} ∩ ((fun ω ↦ ((ω n).2.2, (ω n).1, (ω (n + 1)).2.1)) ⁻¹' E ∩ (fun ω (i : Fin n) ↦ ω i) ⁻¹' H)) =
        (M θ).real ((fun ω ↦ (ω n).2.1) ⁻¹' {y} ∩ (fun ω (i : Fin n) ↦ ω i) ⁻¹' H) *
          ∫ z, ∑ y', (if (z.2.2, z.1, y') ∈ E then (1 : ℝ) else 0) * M.T z.2.1 z.2.2 y' ∂(M.stageK θ y) := by
    intro y E H hE hH
    have hEm : ∀ y', MeasurableSet {z : ℝ × S × A | (z.2.2, z.1, y') ∈ E} := fun y' ↦
      (measurable_snd.snd.prodMk (measurable_fst.prodMk measurable_const)) hE
    have hφ : StronglyMeasurable (fun z : ℝ × S × A ↦ ∑ y', (if (z.2.2, z.1, y') ∈ E then (1 : ℝ) else 0) * M.T z.2.1 z.2.2 y') :=
      (Finset.measurable_sum _ fun y' _ ↦ (Measurable.ite (hEm y') measurable_const measurable_const).mul (hTm y')).stronglyMeasurable
    have hCφ : ∀ z : ℝ × S × A, ‖∑ y', (if (z.2.2, z.1, y') ∈ E then (1 : ℝ) else 0) * M.T z.2.1 z.2.2 y'‖ ≤ Fintype.card S := by
      intro z
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun y' _ ↦ (norm_mul_le _ _).trans
        (mul_le_one₀ (Norm_1.le.One _) (norm_nonneg _) (hT1 _ _ _))).trans ?_)
      simp
    let G : S → (Π _ : Finset.Iic n, ℝ × S × A) → ℝ := fun y' h ↦
      (if (fun i : Fin n ↦ h ⟨i, Finset.mem_Iic.2 i.2.le⟩) ∈ H then (1 : ℝ) else 0) *
        ((if (h ⟨n, Finset.mem_Iic.2 le_rfl⟩).2.1 = y then (1 : ℝ) else 0) *
          (if ((h ⟨n, Finset.mem_Iic.2 le_rfl⟩).2.2, (h ⟨n, Finset.mem_Iic.2 le_rfl⟩).1, y') ∈ E then (1 : ℝ) else 0))
    have hGm : ∀ y', StronglyMeasurable (G y') := fun y' ↦
      (hι ((Measurable.of_eval fun i ↦ measurable_pi_apply _) hH)).mul
        ((hι ((measurable_pi_apply _).snd.fst (measurableSet_singleton y))).mul
          (hι ((measurable_pi_apply _).snd.snd.prodMk ((measurable_pi_apply _).fst.prodMk measurable_const) hE)))
    have hGC : ∀ y' h, ‖G y' h‖ ≤ 1 := fun y' h ↦ by
      simp only [G, norm_mul]
      exact mul_le_one₀ (Norm_1.le.One _) (by positivity)
        (mul_le_one₀ (Norm_1.le.One _) (norm_nonneg _) (Norm_1.le.One _))
    have hint : ∀ y' {g : (ℕ → ℝ × S × A) → ℝ}, Measurable g → (∀ ω, ‖g ω‖ ≤ 1) →
        Integrable (fun ω ↦ G y' (Preorder.frestrictLe n ω) * g ω) (M θ) := fun y' g hg hgC ↦
      Integrable.of_bound (((hGm y').comp_measurable (Preorder.measurable_frestrictLe n)).mul hg.stronglyMeasurable).aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun ω ↦ by
          rw [norm_mul]
          exact mul_le_one₀ (hGC _ _) (norm_nonneg _) (hgC ω))
    rw [← integral_indicator_one (hsm (measurableSet_singleton y) |>.inter ((hXm hE).inter (hHm hH))),
      ← integral_indicator_one ((hsm (measurableSet_singleton y)).inter (hHm hH))]
    calc _ = ∫ ω, ∑ y', G y' (Preorder.frestrictLe n ω) * (if (ω (n + 1)).2.1 = y' then (1 : ℝ) else 0) ∂(M θ) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
          dsimp only
          rw [Finset.sum_eq_single (ω (n + 1)).2.1 (fun b _ hb ↦ by simp [Ne.symm hb]) (by simp)]
          dsimp only [G]
          simp only [Set.indicator_apply, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Pi.one_apply,
            Preorder.frestrictLe_apply, if_true, mul_one]
          by_cases h₁ : (ω n).2.1 = y <;> by_cases h₂ : ((ω n).2.2, (ω n).1, (ω (n + 1)).2.1) ∈ E <;>
            by_cases h₃ : (fun i : Fin n ↦ ω i) ∈ H <;> simp [h₁, h₂, h₃]
      _ = ∑ y', ∫ ω, G y' (Preorder.frestrictLe n ω) * (if (ω (n + 1)).2.1 = y' then (1 : ℝ) else 0) ∂(M θ) :=
          integral_finsetSum _ fun y' _ ↦ hint y' ((StronglyMeasurable_Eq12 (A := A) y').measurable.comp (measurable_pi_apply _))
            fun _ ↦ Norm_1.le.One _
      _ = ∑ y', ∫ ω, G y' (Preorder.frestrictLe n ω) * M.T (ω n).2.1 (ω n).2.2 y' ∂(M θ) := by
          refine Finset.sum_congr rfl fun y' _ ↦ ?_
          rw [Integral_Mul.eq.Integral_Mul_Integral.of.All_LeNorm.StronglyMeasurable.All_LeNorm.StronglyMeasurable (M := M) (hGm y') (hGC y')
            (StronglyMeasurable_Eq12 y') (fun _ ↦ Norm_1.le.One _) θ]
          simp only [hstep1]
      _ = ∫ ω, ∑ y', G y' (Preorder.frestrictLe n ω) * M.T (ω n).2.1 (ω n).2.2 y' ∂(M θ) :=
          (integral_finsetSum _ fun y' _ ↦ hint y' ((hTm y').comp (measurable_pi_apply _)) fun _ ↦ hT1 _ _ _).symm
      _ = ∫ ω, (if (fun i : Fin n ↦ ω i) ∈ H then (1 : ℝ) else 0) * ((if (ω n).2.1 = y then (1 : ℝ) else 0) *
            ∑ y', (if ((ω n).2.2, (ω n).1, y') ∈ E then (1 : ℝ) else 0) * M.T (ω n).2.1 (ω n).2.2 y') ∂(M θ) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
          dsimp only [G]
          simp only [Finset.mul_sum, Preorder.frestrictLe_apply]
          refine Finset.sum_congr rfl fun y' _ ↦ ?_
          by_cases h₁ : (ω n).2.1 = y <;> by_cases h₂ : ((ω n).2.2, (ω n).1, y') ∈ E <;>
            by_cases h₃ : (fun i : Fin n ↦ ω i) ∈ H <;> simp [h₁, h₂, h₃]
      _ = _ := by
          rw [hC n y H hH hφ hCφ]
          refine congrArg (· * _) (integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_))
          by_cases h₁ : (ω n).2.1 = y <;> by_cases h₃ : (fun i : Fin n ↦ ω i) ∈ H <;> simp [h₁, h₃]
  show CondIndepFun (MeasurableSpace.comap (fun ω : ℕ → ℝ × S × A ↦ (ω n).2.1) inferInstance) hsm.comap_le
    (fun ω ↦ ((ω n).2.2, (ω n).1, (ω (n + 1)).2.1)) (fun ω (i : Fin n) ↦ ω i) (M θ)
  rw [condIndepFun_iff_condExp_inter_preimage_eq_mul hXm hHm]
  intro E H hE hH
  have hU : ∀ {U : Set (ℕ → ℝ × S × A)}, MeasurableSet U → Integrable (U.indicator fun _ ↦ (1 : ℝ)) (M θ) :=
    fun hU ↦ (integrable_const 1).indicator hU
  filter_upwards [MEqCondExp_Integral.of.Integrable.Measurable hsm (hU ((hXm hE).inter (hHm hH))),
    MEqCondExp_Integral.of.Integrable.Measurable hsm (hU (hXm hE)),
    MEqCondExp_Integral.of.Integrable.Measurable hsm (hU (hHm hH)),
    Random.AeNe_0 («π» := M θ) (X := fun ω : ℕ → ℝ × S × A ↦ (ω n).2.1)] with ω h₁ h₂ h₃ h₄
  have hB := hsm (measurableSet_singleton (ω n).2.1)
  have hcond : ∀ {U}, MeasurableSet U →
      ∫ ω', U.indicator (fun _ ↦ (1 : ℝ)) ω' ∂(M θ)[|(fun ω ↦ (ω n).2.1) ⁻¹' {(ω n).2.1}] =
        ((M θ).real ((fun ω ↦ (ω n).2.1) ⁻¹' {(ω n).2.1}))⁻¹ * (M θ).real ((fun ω ↦ (ω n).2.1) ⁻¹' {(ω n).2.1} ∩ U) := fun hU ↦ by
    rw [integral_indicator_const _ hU, smul_eq_mul, mul_one]
    simp only [measureReal_def, cond_apply hB, ENNReal.toReal_mul, ENNReal.toReal_inv]
  have hP : (M θ).real ((fun ω ↦ (ω n).2.1) ⁻¹' {(ω n).2.1}) ≠ 0 := (measureReal_eq_zero_iff (measure_ne_top _ _)).not.2 h₄
  have hE' := hK (ω n).2.1 E Set.univ hE MeasurableSet.univ
  simp only [Set.preimage_univ, Set.inter_univ] at hE'
  rw [h₁, h₂, h₃]
  rw [hcond ((hXm hE).inter (hHm hH)), hcond (hXm hE), hcond (hHm hH), hK _ E H hE hH, hE']
  field_simp


-- created on 2026-10-08
