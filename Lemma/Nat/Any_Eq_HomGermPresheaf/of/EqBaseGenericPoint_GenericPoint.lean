import Mathlib
import sympy.Basic

open CategoryTheory AlgebraicGeometry

/--
[AlgebraicGeometry_exists_ringHom_functionField_germ_eq_of_base_genericPoint_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_ringHom_functionField_germ_eq_of_base_genericPoint_eq.lean)
-/
@[path]
private lemma main
  {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
  {f : Y ⟶ X}
-- given
  (hf : f.base (genericPoint Y) = genericPoint X) :
-- imply
  ∃ δ : ↑X.functionField →+* ↑Y.functionField,
      ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (hU' : genericPoint Y ∈ f ⁻¹ᵁ U)
        (sec : X.presheaf.obj (Opposite.op U)),
        δ ((X.presheaf.germ U (genericPoint X) hU).hom sec) =
          (Y.presheaf.germ (f ⁻¹ᵁ U) (genericPoint Y) hU').hom ((f.app U).hom sec) := by
-- proof
  have hspec : f.base (genericPoint Y) ⤳ genericPoint X := hf ▸ specializes_rfl
  refine ⟨(X.presheaf.stalkSpecializes hspec ≫ f.stalkMap (genericPoint Y)).hom, ?_⟩
  intro U hU hU' sec
  have h1 := TopCat.Presheaf.germ_stalkSpecializes X.presheaf hU hspec
  have h2 := Scheme.Hom.germ_stalkMap f U (genericPoint Y) hU'
  have h3 : X.presheaf.germ U (genericPoint X) hU ≫ X.presheaf.stalkSpecializes hspec ≫
      f.stalkMap (genericPoint Y) = f.app U ≫ Y.presheaf.germ (f ⁻¹ᵁ U) (genericPoint Y) hU' := by
    rw [← Category.assoc, h1]
    exact h2
  change (X.presheaf.germ U (genericPoint X) hU ≫ X.presheaf.stalkSpecializes hspec ≫
      f.stalkMap (genericPoint Y)).hom sec = (f.app U ≫ Y.presheaf.germ (f ⁻¹ᵁ U) (genericPoint Y) hU').hom sec
  rw [h3]


-- created on 2026-10-05
