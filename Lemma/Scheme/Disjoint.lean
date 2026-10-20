import Mathlib
import sympy.Basic
open CategoryTheory AlgebraicGeometry IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_disjoint_range_support_ker_of_comp_eq_comp_spec_of_isFractionRing_of_surjective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_disjoint_range_support_ker_of_comp_eq_comp_spec_of_isFractionRing_of_surjective.lean)
-/
@[path]
private lemma main
  {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {k : Type u} [Field k] (toκ : RingHom O k) (hκ : Function.Surjective toκ)
  (T' : Type u) [Field T'] [Algebra O T'] [IsFractionRing O T']
  {X Z W : (Scheme : Type (u + 1))} (q : X ⟶ Spec (CommRingCat.of O)) (f : Z ⟶ X) [QuasiCompact f]
  (hf : ∃ f₀ : Z ⟶ Spec (CommRingCat.of k), f ≫ q = f₀ ≫ Spec.map (CommRingCat.ofHom toκ))
  (g : W ⟶ X) (hg : ∃ g₀ : W ⟶ Spec (CommRingCat.of T'), g ≫ q = g₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap O T'))) :
  -- imply
  Disjoint (Set.range g.base) (f.ker.support : Set X) := by
  -- proof
  obtain ⟨f₀, hf₀⟩ := hf
  obtain ⟨g₀, hg₀⟩ := hg
  have hSpec : ∀ {F : Type u} [Field F] (φ : RingHom O F) (x : Spec (CommRingCat.of F)), ((Spec.map (CommRingCat.ofHom φ)).base x).asIdeal = RingHom.ker φ := by
    intro F _ φ x
    have hx : x.asIdeal = ⊥ := Ideal.eq_bot_of_prime x.asIdeal
    change Ideal.comap φ x.asIdeal = RingHom.ker φ
    rw [hx, ← RingHom.ker_eq_comap_bot]
  have hclosed : IsClosed (q.base ⁻¹' {closedPoint O}) :=
    IsClosed.preimage q.base.hom.continuous (isClosed_singleton_closedPoint (R := O))
  have hrange_f : Set.range f.base ⊆ q.base ⁻¹' {closedPoint O} := by
    rintro _ ⟨z, rfl⟩
    have h := congrArg (fun h => h.base z) hf₀
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    show q.base (f.base z) = closedPoint O
    change q.base (f.base z) = _ at h
    rw [h]
    apply PrimeSpectrum.ext
    rw [hSpec toκ]
    apply IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective toκ hκ)
  have hrange_g : ∀ w, (q.base (g.base w)).asIdeal = ⊥ := by
    intro w
    have h := congrArg (fun h => h.base w) hg₀
    simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h
    change q.base (g.base w) = _ at h
    rw [h, hSpec (algebraMap O T')]
    apply (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective O T')
  rw [Scheme.Hom.support_ker]
  refine Set.disjoint_left.mpr ?_
  rintro _ ⟨w, rfl⟩ hx
  have h1 : q.base (g.base w) = closedPoint O := (closure_minimal hrange_f hclosed) hx
  have h2 := congrArg PrimeSpectrum.asIdeal h1
  rw [hrange_g w] at h2
  apply IsDiscreteValuationRing.not_a_field O h2.symm


-- created on 2026-10-20
