import Mathlib
import sympy.Basic

open CategoryTheory AlgebraicGeometry

/--
[AlgebraicGeometry_Scheme_Hom_stalkMap_genericPoint_surjective_of_forall_exists_div](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_stalkMap_genericPoint_surjective_of_forall_exists_div.lean)
-/
@[main]
private lemma main
  {Y Z : Scheme.{u}} [IsIntegral Y]
  {f : Y ⟶ Z}
  {V : Z.Opens}
-- given
  (hV : f (genericPoint Y) ∈ V)
  (hgen : ∀ x : Y.functionField, ∃ a b : Γ(Z, V), Y.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Y) hV (f.app V b) ≠ 0 ∧ x * Y.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Y) hV (f.app V b) = Y.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Y) hV (f.app V a)) :
-- imply
  Function.Surjective (f.stalkMap (genericPoint Y)) := by
-- proof
  intro x
  obtain ⟨a, b, hb, hx⟩ := hgen x

  let ga := Z.presheaf.germ V (f (genericPoint Y)) hV a
  let gb := Z.presheaf.germ V (f (genericPoint Y)) hV b
  have hga : f.stalkMap (genericPoint Y) ga = Y.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Y) hV (f.app V a) :=
    Scheme.Hom.germ_stalkMap_apply f V (genericPoint Y) hV a
  have hgb : f.stalkMap (genericPoint Y) gb = Y.presheaf.germ (f ⁻¹ᵁ V) (genericPoint Y) hV (f.app V b) :=
    Scheme.Hom.germ_stalkMap_apply f V (genericPoint Y) hV b

  have hunit : IsUnit gb := by
    by_contra h
    have h0 : f.stalkMap (genericPoint Y) gb = 0 := by

      have hnu : ¬ IsUnit (f.stalkMap (genericPoint Y) gb) := fun hu => h ((isUnit_map_iff _ _).mp hu)
      rwa [isUnit_iff_ne_zero, not_not] at hnu
    exact hb (hgb ▸ h0)
  refine ⟨ga * ↑(hunit.unit⁻¹), ?_⟩
  rw [map_mul, hga]
  have hinv : f.stalkMap (genericPoint Y) ↑(hunit.unit⁻¹) = (f.stalkMap (genericPoint Y) gb)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← map_mul, IsUnit.val_inv_mul, map_one])
  rw [hinv, hgb, eq_comm, eq_mul_inv_iff_mul_eq₀ hb, hx]


-- created on 2026-10-05
