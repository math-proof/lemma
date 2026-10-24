import Mathlib
import sympy.Basic
open CategoryTheory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false


/--
[groupCohomology_isZero_H1_and_natCard_H2_and_span_map_of_iso](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_groupCohomology_isZero_H1_and_natCard_H2_and_span_map_of_iso.lean)
-/
@[path]
private lemma main
  {G : Type} [Group G] (A B : Rep ℤ G) (e : A ≅ B) (u : groupCohomology A 2)
  (h1 : ∀ S : Subgroup G, CategoryTheory.Limits.IsZero (groupCohomology (Rep.res S.subtype A) 1))
  (h2 : ∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype A) 2) = Fintype.card S)
  (h3 : ∀ S : Subgroup G,
    Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) 2).hom u} = ⊤) :
  -- imply
  (∀ S : Subgroup G, CategoryTheory.Limits.IsZero (groupCohomology (Rep.res S.subtype B) 1)) ∧
    (∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype B) 2) = Fintype.card S) ∧
    (∀ S : Subgroup G,
      Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype B)) 2).hom
        ((groupCohomology.map (MonoidHom.id G) e.hom 2).hom u)} = ⊤) := by
  -- proof
  let resIso : ∀ S : Subgroup G, Rep.res S.subtype A ≅ Rep.res S.subtype B := fun S =>
    (Rep.resFunctor S.subtype).mapIso e
  let cohIso : ∀ (S : Subgroup G) (n : ℕ),
      groupCohomology (Rep.res S.subtype A) n ≅ groupCohomology (Rep.res S.subtype B) n := fun S n =>
    (groupCohomology.functor ℤ S n).mapIso (resIso S)
  refine ⟨fun S => (h1 S).of_iso (cohIso S 1).symm, fun S _ => ?_, fun S => ?_⟩
  ·
    rw [← h2 S]
    refine Nat.card_congr (cohIso S 2).toLinearEquiv.toEquiv.symm
  ·
    have nat := (groupCohomology.resNatTrans ℤ S.subtype 2).naturality e.hom
    have key : (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype B)) 2).hom
      ((groupCohomology.map (MonoidHom.id G) e.hom 2).hom u) =
      ((cohIso S 2).hom).hom ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) 2).hom u) := by
      have := congrArg (fun φ => (ModuleCat.Hom.hom φ) u) nat
      simp [LinearMap.comp_apply] at this
      refine this
    rw [key]
    have hspan := congrArg (Submodule.map (cohIso S 2).hom.hom) (h3 S)
    rw [Submodule.map_span, Set.image_singleton, Submodule.map_top] at hspan
    rw [hspan, LinearMap.range_eq_top]
    refine (cohIso S 2).toLinearEquiv.surjective


-- created on 2026-10-20
