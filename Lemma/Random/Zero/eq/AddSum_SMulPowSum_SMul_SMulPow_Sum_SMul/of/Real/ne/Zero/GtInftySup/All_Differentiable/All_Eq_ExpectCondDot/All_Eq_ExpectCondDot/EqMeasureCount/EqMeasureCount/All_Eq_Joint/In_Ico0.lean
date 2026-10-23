import Lemma.Random.Grad.eq.Add_SMul_Sum_SMul.of.Ne0Real_Preimage.GtInftySup.All_Differentiable_Prob.All_Eq_Expect.All_Eq_Expect.EqMeasureCount.EqMeasureCount.In_Ico
import Lemma.Random.PnAdd_1.eq.Sum_MulPnP1
import Lemma.Random.RealPreimageS.ne.Zero.of.NePn_0.Ne0Real_Preimage
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Filter Topology Random Measure
open scoped ENNReal.ToRealCoe


/--
Unrolled policy-gradient recursion: for a reachable initial state x (h₆) and every 
,
∇V(s[0] = x) = ∑ t < n, γ ^ t • ∑ y, ℙ(s[t] = y | s[0] = x) • ∑ u, Q(y, u) • ∇π(u | y)
  + γ ^ n • ∑ y, ℙ(s[n] = y | s[0] = x) • ∇V(s[n] = y).
The sympy path integral ∫ ∏ ℙ(s[t+1] | s[t]) over s[1:t+1] is written as the 	-step
conditional probability ℙ(s[t] = y | s[0] = x) (Chapman–Kolmogorov).
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [CountableMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [CountableMeasure A] [MeasurableSingletonClass A] [Fintype A]
  {M : Model Θ S A}
  {θ : Θ}
  {γ : ℝ}
  {x : S}
  {Q : Θ → ℕ → S → A → ℝ}
  {V : Θ → ℕ → S → ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (h₂ : ∀ θ t («s.bvar» : ℕ → S) («a.bvar» : ℕ → A), Q θ t («s.bvar» t) («a.bvar» t) = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t ∧ a t = «a.bvar» t))
  (h₃ : ∀ θ t («s.bvar» : ℕ → S), V θ t («s.bvar» t) = 𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t))
  (h₄ : ∀ x u, Differentiable ℝ (fun θ => M.policy.prob θ x u))
  (h₅ : sup[θ, x, u] ‖∇[θ] M.policy.prob θ x u‖ < ∞)
  (h₆ : (M θ).real (s 0 ⁻¹' {x}) ≠ 0)
  (hP : ∀ θ y, (M θ).real ((fun ω : ℕ → ℝ × S × A ↦ (ω 0).2.1) ⁻¹' {y}) ≠ 0)
  (hπ : ∀ θ y u, (M θ).real ((fun ω : ℕ → ℝ × S × A ↦ (ω 0).2.1) ⁻¹' {y}) * M.policy.prob θ y u ≠ 0)
  (n : ℕ) :
-- imply
  ∇[θ] V θ 0 x =
    ∑ t ∈ Finset.range n, γ ^ t • ∑ y, (M θ)[|s 0 ⁻¹' {x}].real (s t ⁻¹' {y}) •
        ∑ u, Q θ t y u • ∇[θ] M.policy.prob θ y u +
      γ ^ n • ∑ y, (M θ)[|s 0 ⁻¹' {x}].real (s n ⁻¹' {y}) • ∇[θ] V θ n y := by
-- proof
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg (·.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  let Qloc (θ : Θ) (t : ℕ) (x : S) (u : A) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x ∧ a t = u)
  let Vloc (θ : Θ) (t : ℕ) (x : S) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x)
  have hQ : Q = Qloc := funext fun θ => funext fun t => funext fun x => funext fun u =>
    h₂ θ t (fun _ ↦ x) (fun _ ↦ u)
  have hV : V = Vloc := funext fun θ => funext fun t => funext fun x =>
    h₃ θ t (fun _ ↦ x)
  subst hQ hV
  classical
  have h₈ : ∀ t y, (M θ)[|s 0 ⁻¹' {x}].real (s t ⁻¹' {y}) = M.Pn θ t x y := fun t y => by
    have h := RealPreimageSPreimageS_Add.eq.Pn.of.Ne0Real_Preimage (M := M) θ 0 t x y h₁ h₆
    rwa [zero_add] at h
  simp_rw [h₈]
  have hQ_expect : ∀ θ t («s.bvar» : ℕ → S) («a.bvar» : ℕ → A),
      Qloc θ t («s.bvar» t) («a.bvar» t) =
        𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t ∧ a t = «a.bvar» t) :=
    fun _ _ _ _ => rfl
  have hV_expect : ∀ θ t («s.bvar» : ℕ → S),
      Vloc θ t («s.bvar» t) =
        𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = «s.bvar» t) :=
    fun _ _ _ => rfl
  induction n with
  | zero => simp [Pn0.eq.Eq]
  | succ n ih =>
    have h₉ : ∀ y, M.Pn θ n x y • ∇[θ] Vloc θ n y =
        M.Pn θ n x y • (∑ u, Qloc θ n y u • ∇[θ] M.policy.prob θ y u +
          γ • ∑ z, M.P1 θ y z • ∇[θ] Vloc θ (n + 1) z) := by
      intro y
      if hy : M.Pn θ n x y = 0 then
        rw [hy, zero_smul, zero_smul]
      else
        have hReach := RealPreimageS.ne.Zero.of.NePn_0.Ne0Real_Preimage (M := M) θ n x y h₁ h₆ hy
        have h := Grad.eq.Add_SMul_Sum_SMul.of.Ne0Real_Preimage.GtInftySup.All_Differentiable_Prob.All_Eq_Expect.All_Eq_Expect.EqMeasureCount.EqMeasureCount.In_Ico
          («s.bvar» := fun _ ↦ y)
          h₀ h₁ (Q := Qloc) (V := Vloc) hQ_expect hV_expect h₄ h₅ hReach hP (fun θ u => hπ θ y u)
        have hSingle : ∀ θ t, SinglePSpace (M θ) (a t, s t) := fun _ t =>
          SinglePSpace.of.Measurable.Measurable (Random.Measurable.of.All_Eq.snd.snd h₁ t) (Random.Measurable.of.All_Eq.snd.fst h₁ t)
        have hπ_eq : ∀ u, ∇[θ] (ℙ[M θ]((a n) = u | (s n) = y) : ℝ) = ∇[θ] M.policy.prob θ y u := by
          intro u
          have hc : ContinuousAt (fun θ' => (M θ').real (s n ⁻¹' {y})) θ :=
            (Differentiable_RealPreimageS.of.GtInftySup.All_Differentiable_Prob (M := M) h₁ h₄ h₅ n y θ).continuousAt
          refine Filter.EventuallyEq.gradient_eq ?_
          filter_upwards [hc.eventually_ne hReach] with θ' h
          rw [ProbCond.eq.OfRealPol.of.Ne_0 h₁ (hSingle θ' n) h,
            ENNReal.toReal_ofReal (M.policy.nonneg θ' _ _)]
        simp_rw [hπ_eq] at h
        rw [h]
        have hSs : ∀ θ t, SinglePSpace (M θ) (s (t + 1), s t) :=
          fun _ t =>
            SinglePSpace.of.Measurable.Measurable
              (Random.Measurable.of.All_Eq.snd.fst h₁ (t + 1)) (Random.Measurable.of.All_Eq.snd.fst h₁ t)
        have hP1 : ∀ z, (ℙ[M θ]((s (n + 1)) = z | (s n) = y) : ℝ) = M.P1 θ y z := by
          intro z
          have hDiv := ProbCond.eq.Div.of.SinglePSpace inferInstance (π := M θ)
            (x := s (n + 1)) (y := s n) z y
          rw [hDiv, ENNReal.toReal_div, ← RealPreimageSPreimageS_Add_1.eq.P1.of.Ne0Real_Preimage (M := M) θ n y z h₁ hReach]
          rw [measureReal_def, cond_apply (Random.Measurable.of.All_Eq.snd.fst h₁ n (measurableSet_singleton y)),
            ENNReal.toReal_mul, ENNReal.toReal_inv, mul_comm, div_eq_mul_inv]
          congr 1
          ·
            congr 1
            congr 1
            exact Set.inter_comm _ _
        simp_rw [hP1]
    rw [ih, Finset.sum_range_succ, add_assoc]
    congr 1
    rw [Finset.sum_congr rfl fun y _ => h₉ y]
    simp_rw [smul_add, Finset.sum_add_distrib, smul_add]
    congr 1
    simp_rw [PnAdd_1.eq.Sum_MulPnP1, Finset.sum_smul, Finset.smul_sum, smul_smul]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => ?_
    congr 1
    ring


-- created on 2023-03-30
-- updated on 2026-10-23
