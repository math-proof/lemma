import Mathlib
import Initialize.Tactic.Attr.Basic
open MeasureTheory


private lemma setIntegral_restrict_eq_zero
  {X : Type*}
  [MeasurableSpace X]
  (μ : Measure X) [SFinite μ] (k : X × X → ℂ)
  (S : Set X) (hS : MeasurableSet S)
  (hint : IntegrableOn k (S ×ˢ S) (μ.prod μ))
  (hzero : ∀ A ⊆ S, MeasurableSet A → ∀ B ⊆ S, MeasurableSet B → ∫ p in A ×ˢ B, k p ∂(μ.prod μ) = 0) :
  ∀ T : Set (X × X), MeasurableSet T → ∫ p in T, k p ∂((μ.prod μ).restrict (S ×ˢ S)) = 0 := by
  have hSS : MeasurableSet (S ×ˢ S) := hS.prod hS
  have hrw : ∀ T : Set (X × X), MeasurableSet T →
      ∫ p in T, k p ∂((μ.prod μ).restrict (S ×ˢ S)) = ∫ p in T ∩ S ×ˢ S, k p ∂(μ.prod μ) := by
    intro T hT
    rw [Measure.restrict_restrict hT]
  intro T hT
  induction T, hT using MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod with
  | empty => simp
  | basic T hTmem =>
      obtain ⟨A, hA, B, hB, rfl⟩ := hTmem
      rw [hrw _ (hA.prod hB), Set.prod_inter_prod]
      exact hzero _ Set.inter_subset_right (hA.inter hS) _ Set.inter_subset_right (hB.inter hS)
  | compl T hT ih =>
      have hi : Integrable k ((μ.prod μ).restrict (S ×ˢ S)) := hint
      have h := integral_add_compl hT hi
      rw [ih, zero_add] at h
      rw [h]
      have := hzero S subset_rfl hS S subset_rfl hS
      exact this
  | iUnion T hdisj hT ih =>
      have hi : Integrable k ((μ.prod μ).restrict (S ×ˢ S)) := hint
      rw [integral_iUnion hT hdisj hi.integrableOn]
      simp [ih]

private lemma helper_main
  {X : Type*}
  [MeasurableSpace X]
  (μ : Measure X) [SFinite μ]
  (k : X × X → ℂ)
  (S : ℕ → Set X) (hS : ∀ n, MeasurableSet (S n)) (hmono : Monotone S)
  (hcov : ∀ᵐ x ∂μ, x ∈ ⋃ n, S n)
  (hint : ∀ n, IntegrableOn k (S n ×ˢ S n) (μ.prod μ))
  (hzero : ∀ n, ∀ A ⊆ S n, MeasurableSet A → ∀ B ⊆ S n, MeasurableSet B →
    ∫ p in A ×ˢ B, k p ∂(μ.prod μ) = 0) :
  k =ᵐ[μ.prod μ] 0 := by
  have hblock : ∀ n, ∀ᵐ p ∂(μ.prod μ), p ∈ S n ×ˢ S n → k p = 0 := by
    intro n
    have h0 : k =ᵐ[(μ.prod μ).restrict (S n ×ˢ S n)] 0 :=
      (hint n).ae_eq_zero_of_forall_setIntegral_eq_zero
        (fun T hT _ => setIntegral_restrict_eq_zero μ k (S n) (hS n) (hint n) (hzero n) T hT)
    rwa [Filter.EventuallyEq, ae_restrict_iff' ((hS n).prod (hS n))] at h0
  have h1 : ∀ᵐ p ∂(μ.prod μ), p.1 ∈ ⋃ n, S n :=
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae hcov
  have h2 : ∀ᵐ p ∂(μ.prod μ), p.2 ∈ ⋃ n, S n :=
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae hcov
  rw [← ae_all_iff] at hblock
  filter_upwards [hblock, h1, h2] with p hp h1p h2p
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 h1p
  obtain ⟨j, hj⟩ := Set.mem_iUnion.1 h2p
  exact hp (max i j) ⟨hmono (le_max_left i j) hi, hmono (le_max_right i j) hj⟩
/--
[MeasureTheory_ae_prod_eq_zero_of_forall_setIntegral_prod_eq_zero_of_iUnion](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_MeasureTheory_ae_prod_eq_zero_of_forall_setIntegral_prod_eq_zero_of_iUnion.lean)
-/
@[path]
private lemma main
  [MeasurableSpace X]
  {μ : Measure X} [SFinite μ]
  {k : X × X → ℂ}
  {S : ℕ → Set X}
-- given
  (hS : ∀ n, MeasurableSet (S n))
  (hmono : Monotone S)
  (hcov : ∀ᵐ x ∂μ, x ∈ ⋃ n, S n)
  (hint : ∀ n, IntegrableOn k (S n ×ˢ S n) (μ.prod μ))
  (hzero : ∀ n, ∀ A ⊆ S n, MeasurableSet A → ∀ B ⊆ S n, MeasurableSet B → ∫ p in A ×ˢ B, k p ∂(μ.prod μ) = 0) :
-- imply
  k =ᵐ[μ.prod μ] 0 :=
-- proof
  helper_main μ k S hS hmono hcov hint hzero


-- created on 2026-10-23
