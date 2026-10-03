import Mathlib
import sympy.Basic

open AlgebraicGeometry CategoryTheory

/--
[AlgebraicGeometry_LocallyQuasiFinite_of_formallyUnramified_of_locallyOfFiniteType](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_LocallyQuasiFinite_of_formallyUnramified_of_locallyOfFiniteType.lean)
-/
@[main]
private lemma main
  {X Y : AlgebraicGeometry.Scheme}
  {f : X ⟶ Y} [AlgebraicGeometry.FormallyUnramified f] [AlgebraicGeometry.LocallyOfFiniteType f] :
-- imply
  AlgebraicGeometry.LocallyQuasiFinite f := by
-- proof
  rw [locallyQuasiFinite_iff]
  intro U hU V hV e
  have hu : (f.appLE U V e).hom.FormallyUnramified := f.formallyUnramified_appLE hU hV e
  have hft : (f.appLE U V e).hom.FiniteType := f.finiteType_appLE hU hV e
  algebraize [(f.appLE U V e).hom]
  exact inferInstanceAs (Algebra.QuasiFinite Γ(Y, U) Γ(X, V))


-- created on 2026-10-03
