import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_existsUnique_exists_comp_eq_of_isLocalHom_of_forall_ne](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_existsUnique_exists_comp_eq_of_isLocalHom_of_forall_ne.lean)
-/
@[path]
private lemma main
  {R A' : Type u} [CommRing R] [IsLocalRing R] [CommRing A'] [IsLocalRing A']
  (φ : R →+* A') [IsLocalHom φ]
  {N : (Scheme : Type (u + 1))} (g : N ⟶ Spec (CommRingCat.of R))
  (𝒰 : Scheme.OpenCover N)
  (hne : ∀ i k : 𝒰.I₀, i ≠ k → ∀ n ∈ Set.range (𝒰.f i).base ∩ Set.range (𝒰.f k).base, g.base n ≠ IsLocalRing.closedPoint R)
  (s : Spec (CommRingCat.of A') ⟶ N) (hs : s ≫ g = Spec.map (CommRingCat.ofHom φ)) :
  -- imply
  ∃! i : 𝒰.I₀, ∃ s' : Spec (CommRingCat.of A') ⟶ 𝒰.X i, s' ≫ 𝒰.f i = s := by
  -- proof
  classical
  set x₀ : ↥(Spec (CommRingCat.of A')) := IsLocalRing.closedPoint A' with hx₀
  set n : ↥N := s.base x₀ with hn
  have hgn : g.base n = IsLocalRing.closedPoint R := by
    have h1 : g.base n = (s ≫ g).base x₀ := rfl
    rw [h1, hs]
    apply IsLocalRing.comap_closedPoint φ
  have hrange : ∀ i : 𝒰.I₀, n ∈ Set.range (𝒰.f i).base → Set.range s.base ⊆ Set.range (𝒰.f i).base := by
    intro i hi
    rintro _ ⟨x, rfl⟩
    apply ((IsLocalRing.specializes_closedPoint x).map s.base.hom.continuous).mem_open (IsOpenImmersion.isOpen_range (𝒰.f i)) hi
  obtain ⟨i, y, hy⟩ := 𝒰.exists_eq n
  have hni : n ∈ Set.range (𝒰.f i).base := ⟨y, hy⟩
  refine ⟨i, ⟨IsOpenImmersion.lift (𝒰.f i) s (hrange i hni), IsOpenImmersion.lift_fac _ _ _⟩, ?_⟩
  rintro k ⟨s', hs'⟩
  by_contra hki
  have hbase : (𝒰.f k).base (s'.base x₀) = n := by
    rw [hn, ← hs']
    rfl
  refine hne k i hki n ⟨⟨s'.base x₀, hbase⟩, hni⟩ hgn


-- created on 2026-10-20
