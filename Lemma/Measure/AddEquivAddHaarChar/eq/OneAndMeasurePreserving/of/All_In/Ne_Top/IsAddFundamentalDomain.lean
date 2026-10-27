import Mathlib
import Initialize.Tactic.Attr.Basic
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal NNReal Pointwise


private lemma helper_main
  {G : Type*}
  [AddGroup G]
  [TopologicalSpace G]
  [IsTopologicalAddGroup G]
  [LocallyCompactSpace G]
  [MeasurableSpace G]
  [BorelSpace G]
  (μ : Measure G) [μ.IsAddHaarMeasure] [μ.Regular]
  (Γ : AddSubgroup G) [Countable Γ] (F : Set G) (hF : IsAddFundamentalDomain Γ F μ)
  (hFtop : μ F ≠ ⊤) (φ : G ≃ₜ+ G) (hφ : ∀ x : G, φ x ∈ Γ ↔ x ∈ Γ) :
  addEquivAddHaarChar φ = 1 ∧ MeasurePreserving φ μ μ := by
  classical
  have hφm : Measurable (φ : G → G) := φ.continuous.measurable
  set e : G ≃ᵐ G := φ.toHomeomorph.toMeasurableEquiv with he
  have hecoe : (e : G → G) = φ := rfl
  set c : ℝ≥0 := addEquivAddHaarChar φ with hc
  have hcμ : c • μ.map φ = μ := addEquivAddHaarChar_smul_map μ φ
  have hmp : MeasurePreserving (φ : G → G) μ (μ.map φ) := ⟨hφm, rfl⟩
  have hmp' : MeasurePreserving (e : G → G) μ (μ.map φ) := by rwa [hecoe]
  have hsymm : MeasurePreserving (e.symm : G → G) (μ.map φ) μ := hmp'.symm e
  have hφs : ∀ x : G, φ.symm x ∈ Γ ↔ x ∈ Γ := fun x => by
    rw [← hφ (φ.symm x), ContinuousAddEquiv.apply_symm_apply]
  set ε : Γ ≃ Γ :=
    { toFun := fun γ => ⟨φ.symm γ, (hφs γ).mpr γ.2⟩
      invFun := fun γ => ⟨φ γ, (hφ γ).mpr γ.2⟩
      left_inv := fun γ => Subtype.ext (by simp)
      right_inv := fun γ => Subtype.ext (by simp) } with hε
  have hF' : IsAddFundamentalDomain Γ ((φ.toEquiv : G ≃ G) '' F) (μ.map φ) := by
    refine hF.image_of_equiv (φ.toEquiv : G ≃ G) ?_ ε ?_
    ·
      have : ((φ.toEquiv : G ≃ G).symm : G → G) = (e.symm : G → G) := rfl
      rw [this]
      apply hsymm.quasiMeasurePreserving
    ·
      intro γ x
      show φ ((φ.symm (γ : G)) + x) = (γ : G) + φ x
      rw [map_add, ContinuousAddEquiv.apply_symm_apply]
  have himg : ((φ.toEquiv : G ≃ G) '' F) = φ '' F := rfl
  rw [himg] at hF'
  have hac0 : (c • μ.map φ) ≪ μ.map φ := smul_absolutelyContinuous
  have hac : μ ≪ μ.map φ := fun s hs => by
    have h := hac0 hs
    rwa [hcμ] at h
  have hF'' : IsAddFundamentalDomain Γ (φ '' F) μ := hF'.mono hac
  have h1 : μ (φ '' F) = μ F := hF''.measure_eq hF
  have h2 : μ.map φ (φ '' F) = μ F := by
    rw [map_apply₀ hφm.aemeasurable hF'.nullMeasurableSet, Set.preimage_image_eq _ φ.injective]
  have h3 : μ (φ '' F) = (c : ℝ≥0∞) * μ.map φ (φ '' F) := by
    conv_lhs => rw [← hcμ]
    rfl
  rw [h1, h2] at h3
  have hμ0 : μ ≠ 0 := NeZero.ne μ
  have hF0 : μ F ≠ 0 := hF.measure_ne_zero hμ0
  have hc1 : (c : ℝ≥0∞) = 1 := by
    have := (ENNReal.mul_eq_right hF0 hFtop).mp h3.symm
    exact this
  have hc1' : c = 1 := by exact_mod_cast hc1
  refine ⟨hc1', ?_⟩
  have hmap : μ.map φ = μ := by
    have := hcμ
    rwa [hc1', one_smul] at this
  refine ⟨hφm, hmap⟩

open MeasureTheory in
/--
[MeasureTheory_addEquivAddHaarChar_eq_one_and_measurePreserving_of_isAddFundamentalDomain_of_forall_apply_mem_iff](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_MeasureTheory_addEquivAddHaarChar_eq_one_and_measurePreserving_of_isAddFundamentalDomain_of_forall_apply_mem_iff.lean)
-/
@[path]
private lemma main
  [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : MeasureTheory.Measure G} [μ.IsAddHaarMeasure] [μ.Regular]
  {Γ : AddSubgroup G} [Countable Γ]
  {F : Set G}
-- given
  (hF : MeasureTheory.IsAddFundamentalDomain Γ F μ)
  (hFtop : μ F ≠ ⊤)
  (φ : G ≃ₜ+ G)
  (hφ : ∀ x : G, φ x ∈ Γ ↔ x ∈ Γ) :
-- imply
  MeasureTheory.addEquivAddHaarChar φ = 1 ∧ MeasureTheory.MeasurePreserving φ μ μ :=
-- proof
  helper_main μ Γ F hF hFtop φ hφ


-- created on 2026-10-23
