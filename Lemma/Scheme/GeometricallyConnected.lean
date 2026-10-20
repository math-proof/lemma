import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[AlgebraicGeometry_GeometricallyConnected_of_comp_of_surjective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_GeometricallyConnected_of_comp_of_surjective.lean)
-/
@[path]
private lemma main
  {X Y Z : Scheme} {f : X ⟶ Y} {g : Y ⟶ Z}
-- given
  [GeometricallyConnected (f ≫ g)] [Surjective f] :
-- imply
  GeometricallyConnected g := by
-- proof
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ k => ?_⟩
  have hX : ConnectedSpace ↥(pullback (f ≫ g) k) :=
    pullback_of_geometrically (GeometricallyConnected.geometrically_connectedSpace (f := f ≫ g)) K k
  let φ : pullback (f ≫ g) k ⟶ pullback g k :=
    pullback.map (f ≫ g) k g k f (𝟙 _) (𝟙 Z) (Category.comp_id _) (by simp)
  have hφ : Surjective φ :=
    MorphismProperty.pullbackMap (P := @Surjective) ‹Surjective f› inferInstance rfl
      (Category.id_comp _).symm
  rw [connectedSpace_iff_univ, ← hφ.surj.range_eq]
  apply isConnected_range φ.continuous


-- created on 2026-10-20
