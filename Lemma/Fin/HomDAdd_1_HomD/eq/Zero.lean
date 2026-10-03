import Mathlib
import sympy.Basic

open CategoryTheory groupCohomology

/--
[groupCohomology_inhomogeneousCochains_d_d_apply](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_groupCohomology_inhomogeneousCochains_d_d_apply.lean)
-/
@[main]
private lemma main
  {k G : Type} [CommRing k] [Group G]
  {A : Rep.{0} k G}
  {n : ℕ}
  {y : (Fin n → G) → A} :
-- imply
  (inhomogeneousCochains.d A (n + 1)).hom ((inhomogeneousCochains.d A n).hom y) = 0 := by
-- proof
  have h := congrArg (fun T => (ModuleCat.Hom.hom T) y) (inhomogeneousCochains.d_comp_d (A := A) (n := n))
  simpa using h


-- created on 2026-10-03
