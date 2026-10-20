import Lemma.Random.Integral.eq.Sum_Sum_SMul
import Lemma.Random.IntegrableDotPow_Id.of.All_Eq.In_Ico
import Lemma.Random.Integral_MulEqAndEqGetDot.eq.MulMulRealProbQ.of.All_Eq.In_Ico
import Lemma.Random.PSpace_Path.of.All_PSpace
import Lemma.Random.Measurable_G.of.All_Measurable
import Lemma.Real.SMul.eq.Sum_Sum_SMul
import Mathlib.MeasureTheory.Constructions.Polish.Basic
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random Real Filter Measure


/--
`𝔼[G[t] • ψ(s[t], a[t])] = 𝔼[𝔼[G[t] | s[t], a[t]] • ψ(s[t], a[t])]`
-/
@[path]
private lemma main
  [CountableMeasure S] [MeasurableSingletonClass S] [Fintype S]
  [CountableMeasure A] [MeasurableSingletonClass A] [Fintype A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {M : Model Θ S A}
  {γ : ℝ}
  {r : ℕ ⇀ (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × S × A) → S}
  {a : ℕ ⇀ (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ)
  (ψ : S → A → E) :
-- imply
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace
      (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace
      (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).aemeasurable⟩)
  have : ∀ θ, PSpace (M θ) (AsPathRV.path r) := fun _ =>
    PSpace_Path.of.All_PSpace
      (fun t => ⟨(Random.Measurable.of.All_Eq.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) h₁ t).aemeasurable⟩)
  𝔼[r, s, a : M θ](((γ ^ (id : ℕ → ℕ)) @ r[t:]) • ψ (s t) (a t)) =
    𝔼[s, a : M θ](
      𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s[t], a[t]) • ψ (s t) (a t)) := by
-- proof
  intro _ _ _
  classical
  obtain ⟨r⟩ := r
  obtain ⟨s⟩ := s
  obtain ⟨a⟩ := a
  obtain rfl : r = fun t ω ↦ (ω t).1 := funext₂ fun t ω ↦ (congrArg Prod.fst (congrFun (h₁ t) ω)).symm
  obtain rfl : s = fun t ω ↦ (ω t).2.1 := funext₂ fun t ω ↦ (congrArg (·.2.1) (congrFun (h₁ t) ω)).symm
  obtain rfl : a = fun t ω ↦ (ω t).2.2 := funext₂ fun t ω ↦ (congrArg (·.2.2) (congrFun (h₁ t) ω)).symm
  set r : ℕ → (ℕ → ℝ × S × A) → ℝ := fun t ω ↦ (ω t).1
  set s : ℕ → (ℕ → ℝ × S × A) → S := fun t ω ↦ (ω t).2.1
  set a : ℕ → (ℕ → ℝ × S × A) → A := fun t ω ↦ (ω t).2.2
  let Q (θ : Θ) (t : ℕ) (x : S) (u : A) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x ∧ a t = u)
  set G := (γ ^ (id : ℕ → ℕ)) @ r[t:]
  have hsa : Measurable fun p : (ℕ → S) × (ℕ → A) ↦ (p.1 t, p.2 t) :=
    ((measurable_pi_apply t).comp measurable_fst).prodMk
      ((measurable_pi_apply t).comp measurable_snd)
  have hsa3 : Measurable fun p : (ℕ → ℝ) × ((ℕ → S) × (ℕ → A)) ↦ (p.2.1 t, p.2.2 t) :=
    ((measurable_pi_apply t).comp (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_pi_apply t).comp (measurable_snd.comp measurable_snd))
  have hGpath : StronglyMeasurable fun p : (ℕ → ℝ) × ((ℕ → S) × (ℕ → A)) ↦
      ((γ ^ (id : ℕ → ℕ)) @ fun k ↦ p.1 (t + k)) :=
    (Measurable_G.of.All_Measurable
      (r := fun j (p : (ℕ → ℝ) × ((ℕ → S) × (ℕ → A))) => p.1 j)
      (fun j => (measurable_pi_apply j).comp measurable_fst) γ t).stronglyMeasurable
  have hψpath3 : StronglyMeasurable fun p : (ℕ → ℝ) × ((ℕ → S) × (ℕ → A)) ↦
      ψ (p.2.1 t) (p.2.2 t) :=
    StronglyMeasurable.comp_measurable
      (f := fun q : S × A ↦ ψ q.1 q.2) StronglyMeasurable.of_discrete hsa3
  have hQpath : StronglyMeasurable fun p : (ℕ → S) × (ℕ → A) ↦
      𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = p.1 t ∧ a t = p.2 t) :=
    ((measurable_of_countable fun q : S × A =>
        𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = q.1 ∧ a t = q.2)).comp hsa).stronglyMeasurable
  have hψpath2 : StronglyMeasurable fun p : (ℕ → S) × (ℕ → A) ↦ ψ (p.1 t) (p.2 t) :=
    StronglyMeasurable.comp_measurable
      (f := fun q : S × A ↦ ψ q.1 q.2) StronglyMeasurable.of_discrete hsa
  have hL :
    𝔼[r, s, a : M θ](((γ ^ (id : ℕ → ℕ)) @ r[t:]) • ψ (s t) (a t)) =
      ∫ ω, G ω • ψ (s t ω) (a t ω) ∂(M θ) := by
    rw [Expectation.ofRV, expectation_bochner]
    have hx : AEMeasurable
      (Expectation.asRV r, Expectation.asRV s, Expectation.asRV a) (M θ) :=
      PSpace.aemeasurable
    refine (integral_map hx (hGpath.smul hψpath3).aestronglyMeasurable).trans ?_
    simp only [JointRandomSymbol, AsPathRV.path_process]
    rfl
  have hcore :
    ∫ ω, G ω • ψ (s t ω) (a t ω) ∂(M θ) =
      ∫ ω, Q θ t (s t ω) (a t ω) • ψ (s t ω) (a t ω) ∂(M θ) := by
    have hX : Measurable (fun ω : ℕ → ℝ × S × A => (s t ω, a t ω)) :=
      (Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk (Random.Measurable.of.All_Eq.snd.snd h₁ t)
    have hI : ∀ x u, Integrable (fun ω => (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * G ω)
        (M θ) := by
      intro x u
      refine Integrable.of_bound (C := (1 - γ)⁻¹ * |M.env.R|) ?_ ?_
      ·
        exact (((StronglyMeasurable.of_discrete (f := (fun p : S × A => if p.1 = x ∧ p.2 = u then (1:ℝ) else 0))).comp_measurable
          hX).aestronglyMeasurable).mul (IntegrableDotPow_Id.of.All_Eq.In_Ico (M := M) h₀ h₁ θ t).1
      ·
        filter_upwards [All_And_LeNormExtDotPow_Id.of.All_Eq_Joint.In_Ico (M := M) h₀ h₁ θ t] with ω h
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (by split_ifs <;> simp) |>.trans h.2
    rw [Integral.eq.Sum_Sum_SMul (M := M) h₁ θ t (fun y u => Q θ t y u • ψ y u)]
    have hGω : ∀ ω, G ω • ψ (s t ω) (a t ω) =
        ∑ x, ∑ u, ((if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * G ω) • ψ x u :=
      fun ω => SMul.eq.Sum_Sum_SMul (s := s) (a := a) t ω _ ψ
    refine (integral_congr_ae (Filter.Eventually.of_forall hGω)).trans ?_
    rw [integral_finsetSum _ fun x _ => integrable_finsetSum _ fun u _ => (hI x u).smul_const _]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [integral_finsetSum _ fun u _ => (hI x u).smul_const _]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [integral_smul_const, Integral_MulEqAndEqGetDot.eq.MulMulRealProbQ.of.All_Eq.In_Ico (M := M) h₀ h₁ θ t, smul_smul]
  refine hL.trans (hcore.trans ?_)
  symm
  rw [Expectation.ofRV, expectation_bochner]
  have hx : AEMeasurable (AsPathRV.path s, AsPathRV.path a) (M θ) :=
    PSpace.aemeasurable
  refine (integral_map hx (hQpath.smul hψpath2).aestronglyMeasurable).trans ?_
  simp only [JointRandomSymbol, AsPathRV.path_process]
  change ∫ ω, Q θ t (s t ω) (a t ω) • ψ (s t ω) (a t ω) ∂(M θ) =
    ∫ ω, Q θ t (s t ω) (a t ω) • ψ (s t ω) (a t ω) ∂(M θ)
  rfl


-- created on 2026-10-20
