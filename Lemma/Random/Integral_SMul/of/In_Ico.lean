import Lemma.Random.Integral.eq.Sum_Sum_SMul
import Lemma.Random.IntegrableDotPow_Id.of.All_Eq.In_Ico
import Lemma.Random.Integral_MulEqAndEqGetDot.eq.MulMulRealProbQ.of.All_Eq.In_Ico
import Lemma.Real.SMul.eq.Sum_Sum_SMul
open MeasureTheory ProbabilityTheory Topology PolicyGradient PolicyGradient.Model Random Real


/--
`𝔼[G[t] • ψ(s[t], a[t])] = 𝔼[Q(s[t], a[t]) • ψ(s[t], a[t])]`
-/
@[path]
private lemma main
  [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [MeasurableSpace A] [MeasurableSingletonClass A] [Fintype A] [DecidableEq S] [DecidableEq A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {M : Model Θ S A}
  {γ : ℝ}
  {r : ℕ → (ℕ → ℝ × S × A) → ℝ}
  {s : ℕ → (ℕ → ℝ × S × A) → S}
  {a : ℕ → (ℕ → ℝ × S × A) → A}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, (· t) = (r t, s t, a t))
  (θ : Θ)
  (t : ℕ)
  (ψ : S → A → E) :
-- imply
  let Q (θ : Θ) (t : ℕ) (x : S) (u : A) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x ∧ a t = u);
  ∫ ω, ((γ ^ (id : ℕ → ℕ)) @ r[t:]) ω • ψ (s t ω) (a t ω) ∂(M θ) =
    ∫ ω, Q θ t (s t ω) (a t ω) • ψ (s t ω) (a t ω) ∂(M θ) := by
-- proof
  let Q (θ : Θ) (t : ℕ) (x : S) (u : A) : ℝ :=
    𝔼[r : M θ]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t = x ∧ a t = u)
  set G := (γ ^ (id : ℕ → ℕ)) @ r[t:]
  show ∫ ω, G ω • ψ (s t ω) (a t ω) ∂(M θ) =
    ∫ ω, Q θ t (s t ω) (a t ω) • ψ (s t ω) (a t ω) ∂(M θ)
  have hX : Measurable (fun ω : ℕ → ℝ × S × A => (s t ω, a t ω)) := (Random.Measurable.of.All_Eq.snd.fst h₁ t).prodMk (Random.Measurable.of.All_Eq.snd.snd h₁ t)
  have hI : ∀ x u, Integrable (fun ω => (if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) * ((γ ^ (id : ℕ → ℕ)) @ r[t:]) ω)
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
  have hGω : ∀ ω, ((γ ^ (id : ℕ → ℕ)) @ r[t:]) ω • ψ (s t ω) (a t ω) =
      ∑ x, ∑ u, ((if s t ω = x ∧ a t ω = u then (1:ℝ) else 0) *
        ((γ ^ (id : ℕ → ℕ)) @ r[t:]) ω) • ψ x u :=
    fun ω => SMul.eq.Sum_Sum_SMul (s := s) (a := a) t ω _ ψ
  refine (integral_congr_ae (Filter.Eventually.of_forall hGω)).trans ?_
  rw [integral_finsetSum _ fun x _ => integrable_finsetSum _ fun u _ => (hI x u).smul_const _]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [integral_finsetSum _ fun u _ => (hI x u).smul_const _]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [integral_smul_const, Integral_MulEqAndEqGetDot.eq.MulMulRealProbQ.of.All_Eq.In_Ico (M := M) h₀ h₁ θ t, smul_smul]


-- created on 2026-10-06
-- updated on 2026-10-10
