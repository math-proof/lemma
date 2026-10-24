import Mathlib
import sympy.Basic
open MvPowerSeries IsLocalRing


def dropVar
  {σ : Type u}
  {R : Type v}
  [CommRing R]
  (i : σ) (φ : MvPowerSeries σ R) : MvPowerSeries σ R :=
  fun m => if m i = 0 then φ m else 0

private lemma maximalIdeal_eq_comap
  {σ : Type u}
  {R : Type v}
  [CommRing R]
  [IsLocalRing R] :
  maximalIdeal (MvPowerSeries σ R) = (maximalIdeal R).comap (constantCoeff (σ := σ) (R := R)) := by
  ext φ
  rw [Ideal.mem_comap, mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
    isUnit_iff_constantCoeff]

private lemma coeff_dropVar
  {σ : Type u}
  {R : Type v}
  [CommRing R]
  (i : σ) (φ : MvPowerSeries σ R) (m : σ →₀ ℕ) :
  coeff m (dropVar i φ) = if m i = 0 then coeff m φ else 0 := rfl

private lemma mem_span_X_of_constantCoeff_eq_zero
  {σ : Type u}
  {R : Type v}
  [CommRing R]
  [Finite σ] (φ : MvPowerSeries σ R)
  (hφ : constantCoeff φ = 0) : φ ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) := by
  classical
  have := Fintype.ofFinite σ
  suffices h : ∀ (s : Finset σ) (ψ : MvPowerSeries σ R), constantCoeff ψ = 0 →
      (∀ m : σ →₀ ℕ, ¬ (m.support ⊆ s) → coeff m ψ = 0) →
      ψ ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) by
    exact h Finset.univ φ hφ fun m hm => (hm (Finset.subset_univ _)).elim
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro ψ h0 hs
    have : ψ = 0 := by
      ext m
      if hm : m = 0 then
        subst hm; simpa using h0
      else
        rw [map_zero]
        refine hs m fun hsub => hm ?_
        ext j
        have : j ∉ m.support := fun hj => by simpa using hsub hj
        simpa [Finsupp.mem_support_iff] using this
    rw [this]; exact Ideal.zero_mem _
  | insert i s hi ih =>
    intro ψ h0 hs
    have hdiv : (X i : MvPowerSeries σ R) ∣ ψ - dropVar i ψ := by
      rw [X_dvd_iff]
      intro m hm
      rw [map_sub, coeff_dropVar, if_pos hm, sub_self]
    obtain ⟨q, hq⟩ := hdiv
    have hrest : dropVar i ψ ∈ Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) := by
      refine ih _ ?_ ?_
      · rw [← coeff_zero_eq_constantCoeff_apply, coeff_dropVar, if_pos (by simp),
          coeff_zero_eq_constantCoeff_apply, h0]
      ·
        intro m hm
        rw [coeff_dropVar]
        split_ifs with hmi
        ·
          refine hs m fun hsub => hm fun j hj => ?_
          have hj' := hsub hj
          obtain rfl | h := Finset.mem_insert.mp hj'
          · exact absurd hmi (by simpa [Finsupp.mem_support_iff] using hj)
          · exact h
        · rfl
    have : ψ = dropVar i ψ + X i * q := by rw [← hq]; ring
    rw [this]
    exact Ideal.add_mem _ hrest (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩))

private lemma maximalIdeal_eq_map_C_sup_span_X
  {σ : Type u}
  {R : Type v}
  [CommRing R]
  [Finite σ] [IsLocalRing R] :
  maximalIdeal (MvPowerSeries σ R) =
    (maximalIdeal R).map (C (σ := σ) (R := R)) ⊔
      Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) := by
  apply le_antisymm
  ·
    intro φ hφ
    rw [maximalIdeal_eq_comap, Ideal.mem_comap] at hφ
    have hsplit : φ = C (constantCoeff φ) + (φ - C (constantCoeff φ)) := by ring
    rw [hsplit]
    refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hφ))
      (Ideal.mem_sup_right (mem_span_X_of_constantCoeff_eq_zero _ ?_))
    rw [map_sub, constantCoeff_C, sub_self]
  ·
    refine sup_le ?_ ?_
    ·
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rwa [Ideal.mem_comap, maximalIdeal_eq_comap, Ideal.mem_comap, constantCoeff_C]
    ·
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, maximalIdeal_eq_comap, Ideal.mem_comap, constantCoeff_X]
      exact Ideal.zero_mem _

private lemma residue_comp_C_surjective
  {σ : Type u}
  {R : Type v}
  [CommRing R]
  [IsLocalRing R] :
  Function.Surjective (⇑(residue (MvPowerSeries σ R)) ∘ ⇑(C (σ := σ) (R := R))) := by
  intro x
  obtain ⟨φ, rfl⟩ := residue_surjective x
  refine ⟨constantCoeff φ, ?_⟩
  simp only [Function.comp_apply]
  rw [residue_def, residue_def]
  refine (Ideal.Quotient.eq (I := maximalIdeal (MvPowerSeries σ R))).mpr ?_
  rw [maximalIdeal_eq_comap, Ideal.mem_comap, map_sub, constantCoeff_C, sub_self]
  exact Ideal.zero_mem _
/--
[MvPowerSeries_maximalIdeal_eq_map_C_sup_span_X](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_MvPowerSeries_maximalIdeal_eq_map_C_sup_span_X.lean)
-/
@[path]
private lemma main
  {σ : Type u} [Finite σ]
  {R : Type v} [CommRing R] [IsLocalRing R] :
-- imply
  IsLocalRing.maximalIdeal (MvPowerSeries σ R) =
      (IsLocalRing.maximalIdeal R).map (MvPowerSeries.C (σ := σ) (R := R)) ⊔
        Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) :=
  -- proof
  maximalIdeal_eq_map_C_sup_span_X


-- created on 2026-10-23
