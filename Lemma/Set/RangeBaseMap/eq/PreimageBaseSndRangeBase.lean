import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

/--
[AlgebraicGeometry_Scheme_range_pullbackMap_id_id_eq_preimage_range](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_range_pullbackMap_id_id_eq_preimage_range.lean)
-/
@[path]
private lemma main
  {X S T T' : Scheme.{u}}
  {f : X ⟶ S}
  {g : T ⟶ S}
  {g' : T' ⟶ S}
  {i : T' ⟶ T}
-- given
  (e₁ : f ≫ 𝟙 S = 𝟙 X ≫ f)
  (e₂ : g' ≫ 𝟙 S = i ≫ g) :
-- imply
  Set.range (pullback.map f g' f g (𝟙 X) i (𝟙 S) e₁ e₂).base =
      (pullback.snd f g).base ⁻¹' Set.range i.base := by
-- proof
  have h := Scheme.Pullback.range_map f g' f g (𝟙 X) i (𝟙 S) e₁ e₂
  have h1 : Set.range ((𝟙 X : X ⟶ X) : X → X) = Set.univ := by
    ext x
    exact ⟨fun _ => trivial, fun _ => ⟨x, rfl⟩⟩
  rw [h1, Set.preimage_univ, Set.univ_inter] at h
  exact h


-- created on 2026-10-05
