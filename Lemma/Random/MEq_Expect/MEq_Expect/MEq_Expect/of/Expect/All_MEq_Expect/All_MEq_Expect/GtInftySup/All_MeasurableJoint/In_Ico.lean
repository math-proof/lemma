import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Lemma.Random.MeasurableJoint.is.Measurable.Measurable
import sympy.Basic
import sympy.core.power
import sympy.vector.Basic
import sympy.stats.joint_rv
import sympy.concrete.sup
open MeasureTheory


/-- `main` with every conditional expectation written out as Mathlib's `π[f | MeasurableSpace.comap y inferInstance]`. -/
private lemma raw
  [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace A]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {s : ℕ → Ω → S}
  {a : ℕ → Ω → A}
  {r : ℕ → Ω → ℝ}
  {γ R : ℝ}
  {t : ℕ}
  {Q : ℕ → S → A → ℝ}
  {V : ℕ → S → ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, Measurable (r t, s t, a t)) -- joint random variables r, s, a
  (h₂ : ∀ t ω, |r t ω| ≤ R)
  (h₃ : ∀ t, (fun ω ↦ Q t (s t ω) (a t ω)) =ᵐ[π]
    π[(fun ω ↦ (γ ^ (id : ℕ → ℕ)) @ (r · ω)[t:]) | MeasurableSpace.comap (fun ω ↦ (s t ω, a t ω)) inferInstance])
  (h₄ : ∀ t, (fun ω ↦ V t (s t ω)) =ᵐ[π]
    π[(fun ω ↦ (γ ^ (id : ℕ → ℕ)) @ (r · ω)[t:]) | MeasurableSpace.comap (s t) inferInstance])
  (h₅ : π[(fun ω ↦ (γ ^ (id : ℕ → ℕ)) @ (r · ω)[t + 1:]) | MeasurableSpace.comap (fun ω ↦ ((s t ω, a t ω), s (t + 1) ω)) inferInstance] =ᵐ[π]
    π[(fun ω ↦ (γ ^ (id : ℕ → ℕ)) @ (r · ω)[t + 1:]) | MeasurableSpace.comap (s (t + 1)) inferInstance]) :
-- imply
  (fun ω ↦ V t (s t ω)) =ᵐ[π] π[(fun ω ↦ Q t (s t ω) (a t ω)) | MeasurableSpace.comap (s t) inferInstance] ∧
    (fun ω ↦ V t (s t ω)) =ᵐ[π]
      π[(fun ω ↦ r t ω + γ * V (t + 1) (s (t + 1) ω)) | MeasurableSpace.comap (s t) inferInstance] ∧
    (fun ω ↦ Q t (s t ω) (a t ω)) =ᵐ[π]
      π[(fun ω ↦ r t ω + γ * V (t + 1) (s (t + 1) ω)) | MeasurableSpace.comap (fun ω ↦ (s t ω, a t ω)) inferInstance] := by
-- proof
  have hrm : ∀ n, Measurable (r n) := fun n ↦ (Random.Measurable.Measurable.of.MeasurableJoint (h₁ n)).1
  have hsm : ∀ n, Measurable (s n) := fun n ↦
    (Random.Measurable.Measurable.of.MeasurableJoint (Random.Measurable.Measurable.of.MeasurableJoint (h₁ n)).2).1
  have ham : ∀ n, Measurable (a n) := fun n ↦
    (Random.Measurable.Measurable.of.MeasurableJoint (Random.Measurable.Measurable.of.MeasurableJoint (h₁ n)).2).2
  let G : ℕ → Ω → ℝ := fun n ω ↦ (γ ^ (id : ℕ → ℕ)) @ (r · ω)[n:]
  have hG : ∀ n ω, G n ω = ∑' k, γ ^ k * r (n + k) ω := fun _ _ ↦ rfl
  have hb : ∀ n ω k, ‖γ ^ k * r (n + k) ω‖ ≤ γ ^ k * |R| := fun n ω k ↦ by
    rw [norm_mul, norm_pow, Real.norm_of_nonneg h₀.1, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ((h₂ _ _).trans (le_abs_self R)) (pow_nonneg h₀.1 k)
  have hgeo := (hasSum_geometric_of_lt_one h₀.1 h₀.2).mul_right |R|
  have hsum : ∀ n ω, Summable (fun k ↦ γ ^ k * r (n + k) ω) := fun n ω ↦
    Summable.of_norm_bounded hgeo.summable (hb n ω)
  have hGi : ∀ n, Integrable (G n) π := fun n ↦
    Integrable.of_bound (Measurable.tsum fun k ↦ (hrm (n + k)).const_mul _).aestronglyMeasurable
      ((1 - γ)⁻¹ * |R|) (Filter.Eventually.of_forall fun ω ↦ tsum_of_norm_bounded hgeo (hb n ω))
  have hri : Integrable (r t) π :=
    Integrable.of_bound (hrm t).aestronglyMeasurable |R|
      (Filter.Eventually.of_forall fun ω ↦ (Real.norm_eq_abs _).trans_le ((h₂ t ω).trans (le_abs_self R)))
  have hVi : Integrable (fun ω ↦ V (t + 1) (s (t + 1) ω)) π := integrable_condExp.congr (h₄ (t + 1)).symm
  have hrec : G t = r t + γ • G (t + 1) := funext fun ω ↦ by
    show G t ω = r t ω + γ * G (t + 1) ω
    rw [hG, hG, (hsum t ω).tsum_eq_zero_add, ← tsum_mul_left]
    simp only [pow_zero, one_mul, add_zero]
    congr 1
    apply tsum_congr
    intro k
    rw [show t + (k + 1) = t + 1 + k by ring, pow_succ]
    ring
  have h₀₁ : MeasurableSpace.comap (s t) inferInstance ≤ MeasurableSpace.comap (fun ω ↦ (s t ω, a t ω)) inferInstance :=
    (measurable_fst.comp (comap_measurable (fun ω ↦ (s t ω, a t ω)))).comap_le
  have h₁₂ : MeasurableSpace.comap (fun ω ↦ (s t ω, a t ω)) inferInstance ≤ MeasurableSpace.comap (fun ω ↦ ((s t ω, a t ω), s (t + 1) ω)) inferInstance :=
    (measurable_fst.comp (comap_measurable (fun ω ↦ ((s t ω, a t ω), s (t + 1) ω)))).comap_le
  have hm₁ : MeasurableSpace.comap (fun ω ↦ (s t ω, a t ω)) inferInstance ≤ (inferInstance : MeasurableSpace Ω) :=
    ((hsm t).prodMk (ham t)).comap_le
  have hm₂ : MeasurableSpace.comap (fun ω ↦ ((s t ω, a t ω), s (t + 1) ω)) inferInstance ≤ (inferInstance : MeasurableSpace Ω) :=
    (((hsm t).prodMk (ham t)).prodMk (hsm (t + 1))).comap_le
  have hQ : (fun ω ↦ Q t (s t ω) (a t ω)) =ᵐ[π]
      π[(fun ω ↦ r t ω + γ * V (t + 1) (s (t + 1) ω)) | MeasurableSpace.comap (fun ω ↦ (s t ω, a t ω)) inferInstance] := by
    apply (h₃ t).trans
    show π[G t | _] =ᵐ[π] π[r t + γ • (fun ω ↦ V (t + 1) (s (t + 1) ω)) | _]
    rw [hrec]
    apply (condExp_add hri ((hGi _).smul γ) _).trans
    apply Filter.EventuallyEq.trans _ (condExp_add hri (hVi.smul γ) _).symm
    apply Filter.EventuallyEq.add Filter.EventuallyEq.rfl
    apply (condExp_smul _ _ _).trans (Filter.EventuallyEq.trans _ (condExp_smul _ _ _).symm)
    apply Filter.EventuallyEq.const_smul
    apply (condExp_condExp_of_le h₁₂ hm₂).symm.trans
    apply (condExp_congr_ae h₅).trans
    exact condExp_congr_ae (h₄ (t + 1)).symm
  have hV : (fun ω ↦ V t (s t ω)) =ᵐ[π] π[(fun ω ↦ Q t (s t ω) (a t ω)) | MeasurableSpace.comap (s t) inferInstance] :=
    (h₄ t).trans ((condExp_condExp_of_le h₀₁ hm₁).symm.trans (condExp_congr_ae (h₃ t).symm))
  exact ⟨hV, hV.trans ((condExp_congr_ae hQ).trans (condExp_condExp_of_le h₀₁ hm₁)), hQ⟩


/--
Bellman equations on general state / action spaces, stated with σ-algebra conditional expectations
`𝔼[x: π](f x | y₁, …, yₙ)` (= `π[fun ω ↦ f (x ω) | σ(y₁, …, yₙ)]`, Mathlib's `condExp`, see
`Expectation.condSigma`), so no `Fintype`, `Countable` or `MeasurableSingletonClass` is needed on `S` or
`A`; any `MeasurableSpace`, in particular any `ReferenceMeasure`, will do.
`h₃`, `h₄` define the action / state values `Q`, `V` (π-a.e.) as the conditional expected discounted
return `γ ** Stack[k](k) @ r[t:]` given `(s[t], a[t])`, resp. `s[t]`;
`h₅` is the Markov property: given `(s[t], a[t], s[t+1])` the future return only depends on `s[t+1]`.
The finite trajectory model (event conditioning `𝔼[… | s t = x]`) is
`Random.Eq_Expect.Eq_Expect.Eq_Expect.of.All_Eq_Expect.All_Eq_Expect.In_Ico`.
-/
@[main]
private lemma main
  [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace A]
  {π : Measure Ω} [IsProbabilityMeasure π]
  {s : ℕ → Ω → S}
  {a : ℕ → Ω → A}
  {r : ℕ → Ω → ℝ}
  {γ : ℝ}
  {t : ℕ}
  {Q : ℕ → S → A → ℝ}
  {V : ℕ → S → ℝ}
-- given
  (h₀ : γ ∈ Set.Ico 0 1)
  (h₁ : ∀ t, Measurable (r t, s t, a t)) -- joint random variables r, s, a
  (h₂ : sup[t, ω] |r t ω| < ∞)
  (h₃ : ∀ t, Q t (s t) (a t) =ᵐ[π] 𝔼[r: π]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t, a t))
  (h₄ : ∀ t, V t (s t) =ᵐ[π] 𝔼[r: π]((γ ^ (id : ℕ → ℕ)) @ r[t:] | s t))
  (h₅ : 𝔼[r: π]((γ ^ (id : ℕ → ℕ)) @ r[t + 1:] | s t, a t, s (t + 1)) =ᵐ[π] 𝔼[r: π]((γ ^ (id : ℕ → ℕ)) @ r[t + 1:] | s (t + 1))) :
-- imply
  V t (s t) =ᵐ[π] 𝔼[s, a: π](Q t (s t) (a t) | s t) ∧
    V t (s t) =ᵐ[π] 𝔼[r, s: π](r t + γ * V (t + 1) (s (t + 1)) | s t) ∧
    Q t (s t) (a t) =ᵐ[π] 𝔼[r, s: π](r t + γ * V (t + 1) (s (t + 1)) | s t, a t) := by
-- proof
  obtain ⟨R, hR⟩ := h₂
  have h₂ : ∀ t ω, |r t ω| ≤ R := fun t ω ↦ hR (Set.mem_range_self (t, ω))
  have hσ : MeasurableSpace.comap (fun ω ↦ ((s t ω, a t ω), s (t + 1) ω)) inferInstance =
      MeasurableSpace.comap (JointRandomSymbol (s t) (JointRandomSymbol (a t) (s (t + 1)))) inferInstance := by
    apply le_antisymm
    · apply Measurable.comap_le
      exact (show Measurable fun p : S × A × S ↦ ((p.1, p.2.1), p.2.2) by fun_prop).comp
        (comap_measurable (JointRandomSymbol (s t) (JointRandomSymbol (a t) (s (t + 1)))))
    · apply Measurable.comap_le
      exact (show Measurable fun p : (S × A) × S ↦ (p.1.1, p.1.2, p.2) by fun_prop).comp
        (comap_measurable fun ω ↦ ((s t ω, a t ω), s (t + 1) ω))
  apply raw h₀ h₁ h₂ h₃ h₄
  rw [hσ]
  exact h₅


-- created on 2026-10-06
