import Mathlib.Probability.Independence.Conditional
import sympy.Basic
open MeasureTheory ProbabilityTheory MeasurableSpace
open scoped ProbabilityTheory


/--
Doob's characterization of conditional independence of σ-algebras: `m₁` and `m₂` are conditionally
independent given `m'` iff conditioning additionally on `m₂` does not change the conditional
probability of any `t ∈ m₁`, i.e. `μ⟦t | m' ⊔ m₂⟧ =ᵐ[μ] μ⟦t | m'⟧`.
This turns the graphoid rules of conditional independence (weak union, contraction) into the tower
property of the conditional expectation.
-/
@[main]
private lemma main
  {m' m₁ m₂ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ]
-- given
  (hm' : m' ≤ mΩ)
  (hm₁ : m₁ ≤ mΩ)
  (hm₂ : m₂ ≤ mΩ) :
-- imply
  CondIndep m' m₁ m₂ hm' μ ↔ ∀ t, MeasurableSet[m₁] t → μ⟦t | m' ⊔ m₂⟧ =ᵐ[μ] μ⟦t | m'⟧ := by
-- proof
  have hsup : m' ⊔ m₂ ≤ mΩ := sup_le hm' hm₂
  have hind : ∀ (b : Set Ω) (f : Ω → ℝ),
      (b.indicator fun _ ↦ (1 : ℝ)) * f = b.indicator f := by
    intro b f
    ext ω
    by_cases h : ω ∈ b
    · simp [h]
    · simp [h]
  rw [condIndep_iff _ _ _ hm' hm₁ hm₂]
  constructor
  · intro h t ht
    have htm : MeasurableSet[mΩ] t := hm₁ _ ht
    have hint : Integrable (t.indicator fun _ ↦ (1 : ℝ)) μ := (integrable_const (1 : ℝ)).indicator htm
    -- the defining identity of `μ⟦t | m' ⊔ m₂⟧` on the π-system `{g ∩ b | g ∈ m', b ∈ m₂}`
    have key : ∀ g b, MeasurableSet[m'] g → MeasurableSet[m₂] b →
        ∫ x in g ∩ b, (μ⟦t | m'⟧) x ∂μ = ∫ x in g ∩ b, t.indicator (fun _ ↦ (1 : ℝ)) x ∂μ := by
      intro g b hg hb
      have hbm : MeasurableSet[mΩ] b := hm₂ _ hb
      have h1 : μ[b.indicator (μ⟦t | m'⟧) | m'] =ᵐ[μ] fun ω ↦ (μ⟦t | m'⟧) ω * (μ⟦b | m'⟧) ω := by
        rw [← hind]
        have := condExp_mul_of_stronglyMeasurable_right (μ := μ) (m := m')
          (f := b.indicator fun _ ↦ (1 : ℝ)) (g := μ⟦t | m'⟧) stronglyMeasurable_condExp
          (by rw [hind]; exact integrable_condExp.indicator hbm)
          ((integrable_const (1 : ℝ)).indicator hbm)
        filter_upwards [this] with ω hω
        rw [hω, Pi.mul_apply, mul_comm]
      calc ∫ x in g ∩ b, (μ⟦t | m'⟧) x ∂μ
          = ∫ x in g, b.indicator (μ⟦t | m'⟧) x ∂μ := (setIntegral_indicator hbm).symm
        _ = ∫ x in g, (μ[b.indicator (μ⟦t | m'⟧) | m']) x ∂μ :=
            (setIntegral_condExp hm' (integrable_condExp.indicator hbm) hg).symm
        _ = ∫ x in g, (μ⟦t ∩ b | m'⟧) x ∂μ := by
            refine setIntegral_congr_ae (hm' _ hg) ?_
            filter_upwards [h1, h t b ht hb] with ω h1 h2 _
            rw [h1, h2, Pi.mul_apply]
        _ = ∫ x in g, (t ∩ b).indicator (fun _ ↦ (1 : ℝ)) x ∂μ :=
            setIntegral_condExp hm' ((integrable_const (1 : ℝ)).indicator (htm.inter hbm)) hg
        _ = ∫ x in g ∩ b, t.indicator (fun _ ↦ (1 : ℝ)) x ∂μ := by
            rw [setIntegral_indicator (htm.inter hbm), setIntegral_indicator htm, Set.inter_comm t b,
              ← Set.inter_assoc]
    -- extend to all of `m' ⊔ m₂` (π-λ theorem)
    have hall : ∀ u, MeasurableSet[m' ⊔ m₂] u →
        ∫ x in u, (μ⟦t | m'⟧) x ∂μ = ∫ x in u, t.indicator (fun _ ↦ (1 : ℝ)) x ∂μ := by
      let C : Set (Set Ω) := {u | ∃ g b, MeasurableSet[m'] g ∧ MeasurableSet[m₂] b ∧ u = g ∩ b}
      have hC : IsPiSystem C := by
        rintro _ ⟨g₁, b₁, hg₁, hb₁, rfl⟩ _ ⟨g₂, b₂, hg₂, hb₂, rfl⟩ _
        refine ⟨g₁ ∩ g₂, b₁ ∩ b₂, hg₁.inter hg₂, hb₁.inter hb₂, ?_⟩
        ext ω
        simp only [Set.mem_inter_iff]
        tauto
      have hgen : m' ⊔ m₂ = generateFrom C := by
        apply le_antisymm
        · refine sup_le ?_ ?_
          · intro g hg
            exact measurableSet_generateFrom ⟨g, Set.univ, hg, MeasurableSet.univ, by simp⟩
          · intro b hb
            exact measurableSet_generateFrom ⟨Set.univ, b, MeasurableSet.univ, hb, by simp⟩
        · refine generateFrom_le ?_
          rintro _ ⟨g, b, hg, hb, rfl⟩
          exact ((le_sup_left : m' ≤ m' ⊔ m₂) _ hg).inter ((le_sup_right : m₂ ≤ m' ⊔ m₂) _ hb)
      intro u hu
      induction u, hu using MeasurableSpace.induction_on_inter hgen hC with
      | empty => simp
      | basic u hu =>
        obtain ⟨g, b, hg, hb, rfl⟩ := hu
        exact key g b hg hb
      | compl u hum ih =>
        have huniv := key Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
        rw [Set.inter_self, setIntegral_univ, setIntegral_univ] at huniv
        rw [setIntegral_compl (hsup _ hum) integrable_condExp, setIntegral_compl (hsup _ hum) hint,
          ih, huniv]
      | iUnion f hf hfm ih =>
        rw [integral_iUnion (fun n ↦ hsup _ (hfm n)) hf integrable_condExp.integrableOn,
          integral_iUnion (fun n ↦ hsup _ (hfm n)) hf hint.integrableOn]
        exact tsum_congr ih
    exact (ae_eq_condExp_of_forall_setIntegral_eq hsup hint
      (fun _ _ _ ↦ integrable_condExp.integrableOn) (fun u hu _ ↦ hall u hu)
      ((stronglyMeasurable_condExp (m := m') (μ := μ) (f := t.indicator fun _ ↦ (1 : ℝ))).mono
        (le_sup_left : m' ≤ m' ⊔ m₂)).aestronglyMeasurable).symm
  · intro h t₁ t₂ ht₁ ht₂
    have ht₁m : MeasurableSet[mΩ] t₁ := hm₁ _ ht₁
    have ht₂m : MeasurableSet[mΩ] t₂ := hm₂ _ ht₂
    have hi₁ : Integrable (t₁.indicator fun _ ↦ (1 : ℝ)) μ := (integrable_const (1 : ℝ)).indicator ht₁m
    have hi₂ : Integrable (t₂.indicator fun _ ↦ (1 : ℝ)) μ := (integrable_const (1 : ℝ)).indicator ht₂m
    have hprod : (t₁ ∩ t₂).indicator (fun _ ↦ (1 : ℝ)) =
        (t₂.indicator fun _ ↦ (1 : ℝ)) * t₁.indicator fun _ ↦ (1 : ℝ) := by
      rw [hind, Set.indicator_indicator, Set.inter_comm]
    have hsm : StronglyMeasurable[m' ⊔ m₂] (t₂.indicator fun _ ↦ (1 : ℝ)) :=
      stronglyMeasurable_const.indicator ((le_sup_right : m₂ ≤ m' ⊔ m₂) _ ht₂)
    have hb : ∀ᵐ ω ∂μ, ‖(t₂.indicator fun _ ↦ (1 : ℝ)) ω‖ ≤ 1 := by
      refine Filter.Eventually.of_forall fun ω ↦ ?_
      by_cases h : ω ∈ t₂
      · simp [h]
      · simp [h]
    rw [hprod]
    calc μ[(t₂.indicator fun _ ↦ (1 : ℝ)) * t₁.indicator fun _ ↦ (1 : ℝ) | m']
        =ᵐ[μ] μ[μ[(t₂.indicator fun _ ↦ (1 : ℝ)) * t₁.indicator fun _ ↦ (1 : ℝ) | m' ⊔ m₂] | m'] :=
          (condExp_condExp_of_le le_sup_left hsup).symm
      _ =ᵐ[μ] μ[(t₂.indicator fun _ ↦ (1 : ℝ)) * μ⟦t₁ | m' ⊔ m₂⟧ | m'] :=
          condExp_congr_ae (condExp_stronglyMeasurable_mul_of_bound hsup hsm hi₁ 1 hb)
      _ =ᵐ[μ] μ[(t₂.indicator fun _ ↦ (1 : ℝ)) * μ⟦t₁ | m'⟧ | m'] :=
          condExp_congr_ae ((h t₁ ht₁).mono fun ω hω ↦ by simp only [Pi.mul_apply, hω])
      _ =ᵐ[μ] μ⟦t₂ | m'⟧ * μ⟦t₁ | m'⟧ :=
          condExp_mul_of_stronglyMeasurable_right stronglyMeasurable_condExp
            (by rw [hind]; exact integrable_condExp.indicator ht₂m) hi₂
      _ = μ⟦t₁ | m'⟧ * μ⟦t₂ | m'⟧ := mul_comm _ _


-- created on 2026-10-06