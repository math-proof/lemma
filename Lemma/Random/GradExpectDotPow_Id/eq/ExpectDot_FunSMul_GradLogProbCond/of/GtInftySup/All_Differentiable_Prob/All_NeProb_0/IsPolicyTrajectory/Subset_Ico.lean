import Lemma.Random.GradExpectDotPow_Id.eq.ExpectDot_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_LeSum.CountableMeasure.Subset_Ico
import Lemma.Random.PSpace_Path.of.All_PSpace
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
open scoped ENNReal.ToRealCoe
open Finset (range)
open MeasureTheory ProbabilityTheory PolicyGradient PolicyGradient.DensityModel Filter Topology Random Measure Real IsPolicyTrajectory
set_option maxHeartbeats 900000


/--
Generalized advantage estimation (Schulman et al., arXiv 1506.02438, Eq. (16)) for a
fully discrete MDP: both state and action alphabets are finite and use counting measure,
so `π_θ(· | s)` is an ordinary probability mass function (FunSMul / discrete GAE).

Chess-RL application: take `𝒮` as the finite set of boards (or board+side-to-move
positions) and `𝒜` as the finite legal-move alphabet. A parameterized policy
`M.policy.prob θ x u` — equivalently the stage-0 conditional
`ℙ[M θ](a[0] = «\sf{a}»[0] | s[0] = «\sf{s}»[0])` — is then a move distribution over
legal moves at a board. This lemma is the solid GAE identity used in that setting: the
gradient of the discounted return equals a GAE-weighted score expectation under the
policy trajectory law, with value baseline `V_θ[t] δ k := M.V0 θ γ (δ k)`.
-/
@[path]
private lemma main
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [FiniteDimensional ℝ Θ]
  [CountableMeasure 𝒮] [MeasurableSingletonClass 𝒮] [Fintype 𝒮]
  [CountableMeasure 𝒜] [MeasurableSingletonClass 𝒜] [Fintype 𝒜]
  {M : DensityModel Θ 𝒮 𝒜}
  {θ : Θ}
  {γ ℓ : ℝ}
  {r : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → ℝ}
  {s : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒮}
  {a : ℕ ⇀ (ℕ → ℝ × 𝒮 × 𝒜) → 𝒜}
-- given
  (h₀ : {γ, ℓ} ⊆ Set.Ico 0 1)
  (hπ : DensityModel.IsConditionalProbability M r s a)
  (h₂ : ∀ («\sf{s}» : ℕ ⇀ 𝒮) («\sf{a}» : ℕ ⇀ 𝒜),
    Differentiable ℝ (fun θ => (ℙ[M θ](a[0] = «\sf{a}»[0] | s[0] = «\sf{s}»[0]) : ℝ)))
  (h₃ : sup[θ, «\sf{s}» : ℕ ⇀ 𝒮, «\sf{a}» : ℕ ⇀ 𝒜]
    ‖∇[θ] (ℙ[M θ](a[0] = «\sf{a}»[0] | s[0] = «\sf{s}»[0]) : ℝ)‖ < ∞) :
-- imply
  have : ∀ θ t, SinglePSpace (M θ) (a t, s t) := fun θ t =>
    hπ.htr.singlePSpace_as (haj := hπ.haj) θ t
  have : ∀ θ', PSpace (M θ') (AsPathRV.path r) := fun _ =>
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) hπ.htr.stage_eq t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path s) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.fst (r := ⇑r) (s := ⇑s) (a := ⇑a) hπ.htr.stage_eq t).aemeasurable⟩)
  have : PSpace (M θ) (AsPathRV.path a) :=
    PSpace_Path.of.All_PSpace (fun t => ⟨(Random.Measurable.of.All_Eq.snd.snd (r := ⇑r) (s := ⇑s) (a := ⇑a) hπ.htr.stage_eq t).aemeasurable⟩)
  let : MeasurableSpace Θ := borel Θ
  let V_θ : ℕ ⇀ (ℕ → 𝒮) → ℕ → ℝ := ⟨fun _ δ k => M.V0 θ γ (δ k)⟩
  ∇[θ] 𝔼[r: M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ r) =
    𝔼[r, s, a : M θ]((γ ^ (id : ℕ → ℕ)) ⬝ᵥ fun t ↦
      (((1 - ℓ) * ((ℓ ^ (id : ℕ → ℕ)) ⬝ᵥ fun k ↦ (γ ^ range (k + 1)) ⬝ᵥ
        (r[t:] + γ • V_θ[t + 1] s[t + 1:] - V_θ[t] s[t:]))) •
        ∇[θ] (ℙ[M θ](a[t] | s[t]) : ℝ).log)) := by
-- proof
  -- stage-t conditional = stage-0 via factor (both equal policy.prob)
  have hstage : ∀ θ' t (x : 𝒮) (u : 𝒜),
      (ℙ[M θ'](a[t] = u | s[t] = x) : ℝ) = (ℙ[M θ'](a[0] = u | s[0] = x) : ℝ) :=
    fun θ' t x u =>
      (hπ.factor θ' t x u).symm.trans (hπ.factor θ' 0 x u)
  -- dens CM Diff is on the path-binder conditional; rewrite via hstage
  have hDiff : ∀ t («\sf{s}» : ℕ ⇀ 𝒮) («\sf{a}» : ℕ ⇀ 𝒜),
      Differentiable ℝ (fun θ => (ℙ[M θ](a[t] = «\sf{a}»[t] | s[t] = «\sf{s}»[t]) : ℝ)) :=
    fun t sb ab =>
      (funext fun θ' => hstage θ' t (sb t) (ab t)) ▸
        h₂ ⟨fun _ => sb t⟩ ⟨fun _ => ab t⟩
  -- dens CM ∃g Finset-sum witness from uniform ‖∇ℙ‖ bound + Fintype 𝒜
  have hExistG : ∃ (g : 𝒮 → 𝒜 → ℝ),
      (∀ θ t («\sf{s}» : ℕ ⇀ 𝒮) («\sf{a}» : ℕ ⇀ 𝒜),
        ‖∇[θ] (ℙ[M θ](a[t] = «\sf{a}»[t] | s[t] = «\sf{s}»[t]) : ℝ)‖ ≤
          g «\sf{s}»[t] «\sf{a}»[t]) ∧
      (sup[x] (∑ u, g x u) < ∞) := by
    obtain ⟨C, hC⟩ := h₃
    let g : 𝒮 → 𝒜 → ℝ := fun _ _ => C
    refine ⟨g, ⟨?_, ?_⟩⟩
    · intro θ' t sb ab
      simpa [funext fun θ'' => hstage θ'' t (sb t) (ab t)] using
        hC ⟨(θ', (⟨fun _ => sb t⟩, ⟨fun _ => ab t⟩)), rfl⟩
    · refine ⟨C * (Fintype.card 𝒜 : ℝ), ?_⟩
      rintro _ ⟨x, rfl⟩
      simp [g, Finset.sum_const, nsmul_eq_mul, mul_comm]
  -- dens CM score bound; finite 𝒮×𝒜 ⇒ BddAbove automatically
  have hMs : sup[«\sf{s}» : ℕ ⇀ 𝒮, «\sf{a}» : ℕ ⇀ 𝒜]
      ‖∇[θ] (ℙ[M θ](a[0] = «\sf{a}»[0] | s[0] = «\sf{s}»[0]) : ℝ).log‖ < ∞ := by
    have hfin : BddAbove (Set.range fun z : 𝒮 × 𝒜 =>
        ‖∇[θ] (ℙ[M θ](a[0] = z.2 | s[0] = z.1) : ℝ).log‖) :=
      Set.Finite.bddAbove (Set.finite_range _)
    obtain ⟨Ms, hUB⟩ := hfin
    refine ⟨Ms, ?_⟩
    rintro _ ⟨⟨sb, ab⟩, rfl⟩
    exact hUB ⟨(sb[0], ab[0]), rfl⟩
  exact GradExpectDotPow_Id.eq.ExpectDot_SMul_GradLogProbCond.of.GtInftySup.All_Differentiable_Prob.All_LeSum.CountableMeasure.Subset_Ico
    h₀ hπ hDiff hExistG hMs


-- created on 2026-10-21
-- updated on 2026-11-11
