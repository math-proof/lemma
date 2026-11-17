import Def.Analysis.Calculus.Gradient.Operators.Part2
import Lemma.Random.GradExpectDotPow_Id.eq.ExpectDot_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_LeSum.CountableMeasure.Subset_Ico
import Lemma.Random.PSpace_Path.of.All_PSpace
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
open scoped ENNReal.ToRealCoe
open Finset (range)
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.Model Filter Topology Random Measure Real IsPolicyTrajectory
set_option maxHeartbeats 900000


/--
Generalized advantage estimation (Schulman et al., arXiv 1506.02438, Eq. (16)) for a
fully discrete MDP: both state and action alphabets are finite and use counting measure,
so `π_θ(· | s)` is an ordinary probability mass function (FunSMul / discrete GAE).
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [CountableMeasure 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮] [Nonempty 𝒮] [StandardBorelSpace 𝒮]
  [CountableMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Fintype 𝒜]
  {M : Model Θ 𝒮 𝒜} [hStoch : StochasticPolicy M.toPolicy] [Model.HasMeasurableEnv M]
  {θ : Θ}
  {γ ℓ : ℝ}
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : {γ, ℓ} ⊆ Set.Ico 0 1)
  (hπ : Model.IsConditionalProbability M r s a)
  (h₂ : ∀ («\sf{s}» : ℕ ⇀ 𝒮) («\sf{a}» : ℕ ⇀ 𝒜),
    Differentiable ℝ (fun θ => (ℙ[M.traj θ](a[0] = «\sf{a}»[0] | s[0] = «\sf{s}»[0]) : ℝ)))
  (h₃ : sup[θ, «\sf{s}» : ℕ ⇀ 𝒮, «\sf{a}» : ℕ ⇀ 𝒜]
    ‖∇[θ] (ℙ[M.traj θ](a[0] = «\sf{a}»[0] | s[0] = «\sf{s}»[0]) : ℝ)‖ < ∞) :
-- imply
  have : ∀ θ t, SinglePSpace (M.traj θ) (a t, s t) := fun θ t =>
    hπ.htr.singlePSpace_as (haj := hπ.haj) θ t
  have : ∀ θ', PSpace (M.traj θ') (AsPathRV.path r) := fun _ =>
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) hπ.htr.stage_eq t).aemeasurable⟩)
  have : PSpace (M.traj θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) hπ.htr.stage_eq t).aemeasurable⟩)
  have : PSpace (M.traj θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) hπ.htr.stage_eq t).aemeasurable⟩)
  let : MeasurableSpace Θ := borel Θ
  let V_θ : ℕ ⇀ (ℕ → 𝒮) → ℕ → ℝ := ⟨fun t δ k => M.V θ γ (t + k) (δ k)⟩
  ∇[θ] 𝔼[r: M.traj θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r) =
    𝔼[r, s, a : M.traj θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
      (((1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) ⬝ᵥ fun k ↦ (γ ^ range (k + 1)) ⬝ᵥ
        (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:]))) •
        ∇[θ] (ℙ[M.traj θ](a[t] | s[t]) : ℝ).log)) := by
-- proof
  -- stage-t conditional = stage-0 via factor (both equal policy.π)
  have hstage : ∀ θ' t (sₜ : 𝒮) (aₜ : 𝒜),
      (ℙ[M.traj θ'](a[t] = aₜ | s[t] = sₜ) : ℝ) = (ℙ[M.traj θ'](a[0] = aₜ | s[0] = sₜ) : ℝ) :=
    fun θ' t x u =>
      (hπ.factor θ' t x u).symm.trans (hπ.factor θ' 0 x u)
  -- dens CM Diff is on the path-binder conditional; rewrite via hstage
  have hDiff : ∀ t («\sf{s}» : ℕ ⇀ 𝒮) («\sf{a}» : ℕ ⇀ 𝒜),
      Differentiable ℝ (fun θ => (ℙ[M.traj θ](a[t] = «\sf{a}»[t] | s[t] = «\sf{s}»[t]) : ℝ)) :=
    fun t sb ab =>
      (funext fun θ' => hstage θ' t (sb t) (ab t)) ▸
        h₂ ⟨fun _ => sb t⟩ ⟨fun _ => ab t⟩
  -- dens CM ∃g Finset-sum witness from uniform ‖∇ℙ‖ bound + Fintype 𝒜
  have hExistG : sup[x] (∑ u, sSup (Set.range fun θ => ‖∇[θ] (ℙ[M.traj θ](a[0] = u | s[0] = x) : ℝ)‖)) < ∞ := by
    obtain ⟨C, hC⟩ := h₃
    refine ⟨C * (Fintype.card 𝒜 : ℝ), ?_⟩
    rintro _ ⟨x, rfl⟩
    have hle : ∀ u, sSup (Set.range fun θ => ‖∇[θ] (ℙ[M.traj θ](a[0] = u | s[0] = x) : ℝ)‖) ≤ C := by
      intro u
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨κ, rfl⟩
      simpa using hC ⟨(κ, (⟨fun _ => x⟩, ⟨fun _ => u⟩)), rfl⟩
    calc
      ∑ u, sSup (Set.range fun θ => ‖∇[θ] (ℙ[M.traj θ](a[0] = u | s[0] = x) : ℝ)‖)
          ≤ ∑ _u : 𝒜, C := Finset.sum_le_sum fun u _ => hle u
      _ = C * (Fintype.card 𝒜 : ℝ) := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- dens CM score bound; finite 𝒮×𝒜 ⇒ BddAbove automatically
  have hMs : sup[«\sf{s}» : ℕ ⇀ 𝒮, «\sf{a}» : ℕ ⇀ 𝒜]
      ‖∇[θ] (ℙ[M.traj θ](a[0] = «\sf{a}»[0] | s[0] = «\sf{s}»[0]) : ℝ).log‖ < ∞ := by
    have hfin : BddAbove (Set.range fun z : 𝒮 × 𝒜 =>
        ‖∇[θ] (ℙ[M.traj θ](a[0] = z.2 | s[0] = z.1) : ℝ).log‖) :=
      Set.Finite.bddAbove (Set.finite_range _)
    obtain ⟨Ms, hUB⟩ := hfin
    refine ⟨Ms, ?_⟩
    rintro _ ⟨⟨sb, ab⟩, rfl⟩
    exact hUB ⟨(sb[0], ab[0]), rfl⟩
  have hBdd : ∀ x u, BddAbove (Set.range fun θ => ‖∇[θ] (ℙ[M.traj θ](a[0] = u | s[0] = x) : ℝ)‖) := by
    intro x u
    obtain ⟨C, hC⟩ := h₃
    refine ⟨C, ?_⟩
    rintro _ ⟨κ, rfl⟩
    simpa using hC ⟨(κ, (⟨fun _ => x⟩, ⟨fun _ => u⟩)), rfl⟩
  exact GradExpectDotPow_Id.eq.ExpectDot_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_LeSum.CountableMeasure.Subset_Ico
    h₀ hπ hDiff hExistG hBdd hMs


-- created on 2026-10-21
-- updated on 2026-11-16
