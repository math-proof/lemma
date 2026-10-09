import Mathlib
import sympy.Basic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry

/--
[AlgebraicGeometry_GeometricallyIntegral_isIntegral_of_flat_of_universallyOpen](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_GeometricallyIntegral_isIntegral_of_flat_of_universallyOpen.lean)
-/

private lemma  finite_irreducibleComponents_of_irreducibleSpace (S : Type*) [TopologicalSpace S]
    [IrreducibleSpace S] : (irreducibleComponents S).Finite := by
  refine (Set.finite_singleton (Set.univ : Set S)).subset ?_
  intro Z hZ
  rw [Set.mem_singleton_iff]
  exact hZ.eq_of_le (IrreducibleSpace.isIrreducible_univ S) (Set.subset_univ Z)
@[path]
private lemma main
  {X S : Scheme.{u}} [IsIntegral S]
  {f : X ⟶ S} [GeometricallyIntegral f] [Flat f] [UniversallyOpen f] :
-- imply
  IsIntegral X := by
-- proof
  have : Finite (irreducibleComponents S) :=
    (finite_irreducibleComponents_of_irreducibleSpace S).to_subtype
  rw [isIntegral_iff_irreducibleSpace_and_isReduced]
  exact ⟨GeometricallyIrreducible.irreducibleSpace f f.isOpenMap,
    GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents f⟩


-- created on 2026-10-05
