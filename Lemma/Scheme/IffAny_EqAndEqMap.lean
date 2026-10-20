import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[AlgebraicGeometry_exists_section_comp_eq_iff_factors_of_universallyClosed_of_valuationRing](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_section_comp_eq_iff_factors_of_universallyClosed_of_valuationRing.lean)
-/
@[path]
private lemma main
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {X Xf X' : Scheme.{u}} (g : X ⟶ Spec (.of R))
    (i : Xf ⟶ X) [IsOpenImmersion i] [UniversallyClosed (i ≫ g)]
    (j : X' ⟶ X)
    (hcover : Set.range i ∪ Set.range j = Set.univ)
    (hempty : IsLocalRing.closedPoint R ∉ Set.range (j ≫ g))
    (x : Spec (.of K) ⟶ X) (hx : x ≫ g = Spec.map (CommRingCat.ofHom (algebraMap R K))) :
    (∃ s : Spec (.of R) ⟶ X, s ≫ g = 𝟙 _ ∧ Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ s = x) ↔
      ∃ xf : Spec (.of K) ⟶ Xf, xf ≫ i = x := by
  constructor
  · rintro ⟨s, hsg, hsx⟩
    have hgs : g (s (IsLocalRing.closedPoint R)) = IsLocalRing.closedPoint R := by
      rw [← Scheme.Hom.comp_apply, hsg]
      rfl
    have hc : s (IsLocalRing.closedPoint R) ∈ Set.range i := by
      have hmem : s (IsLocalRing.closedPoint R) ∈ Set.range i ∪ Set.range j :=
        hcover ▸ Set.mem_univ _
      rcases hmem with h | ⟨y, hy⟩
      · exact h
      · exact absurd ⟨y, by rw [Scheme.Hom.comp_apply, hy, hgs]⟩ hempty
    have hsub : Set.range s ⊆ Set.range i := by
      rintro _ ⟨t, rfl⟩
      exact ((IsLocalRing.specializes_closedPoint t).map s.continuous).mem_open
        (IsOpenImmersion.isOpen_range i) hc
    refine ⟨Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ IsOpenImmersion.lift i s hsub, ?_⟩
    rw [Category.assoc, IsOpenImmersion.lift_fac, hsx]
  · rintro ⟨xf, rfl⟩
    have H : ValuativeCriterion.Existence (i ≫ g) := by
      have h : UniversallyClosed (i ≫ g) := inferInstance
      rw [UniversallyClosed.eq_valuativeCriterion] at h
      exact h.1
    let S : ValuativeCommSq (i ≫ g) :=
      { R := R, K := K, i₁ := xf, i₂ := 𝟙 _, commSq := ⟨by simpa using hx⟩ }
    obtain ⟨l, hl₁, hl₂⟩ := (H S).exists_lift
    dsimp only [S] at hl₁ hl₂
    exact ⟨l ≫ i, by simpa using hl₂, by rw [← Category.assoc, hl₁]⟩

-- created on 2026-10-20
