import Mathlib
import sympy.Basic

open CategoryTheory AlgebraicGeometry

/--
[AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected.lean)
-/
@[path]
private lemma main
  {X Y : Scheme.{u}}
  {f : X ⟶ Y} [GeometricallyIrreducible f] :
-- imply
  GeometricallyConnected f := by
-- proof
  refine ⟨?_⟩
  have h := GeometricallyIrreducible.geometrically_irreducibleSpace (f := f)
  rw [geometrically_eq_universally] at h ⊢
  refine MorphismProperty.universally_mono ?_ _ h
  intro X' Y' g hg hI hS
  have : IrreducibleSpace X' := hg hI hS
  infer_instance


-- created on 2026-10-05
