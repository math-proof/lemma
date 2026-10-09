import Mathlib
import sympy.Basic

open CategoryTheory AlgebraicGeometry

/--
[AlgebraicGeometry_isReduced_of_flat_of_surjective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isReduced_of_flat_of_surjective.lean)
-/
@[path]
private lemma main
  {X Y : Scheme.{u}} [IsReduced X]
  {f : X ⟶ Y} [Flat f] [Surjective f] :
-- imply
  IsReduced Y := by
-- proof
  have : ∀ y : Y, _root_.IsReduced (Y.presheaf.stalk y) := by
    intro y
    obtain ⟨x, rfl⟩ := f.surjective y
    let φ := (f.stalkMap x).hom
    let := φ.toAlgebra
    have : Module.Flat (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) := Flat.stalkMap f x
    have : IsLocalHom (algebraMap (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom φ)
    have : Module.FaithfullyFlat (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact isReduced_of_injective (algebraMap (Y.presheaf.stalk (f.base x)) (X.presheaf.stalk x))
      (FaithfulSMul.algebraMap_injective _ _)
  exact isReduced_of_isReduced_stalk Y


-- created on 2026-10-05
