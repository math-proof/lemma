import Mathlib
import sympy.Basic

open CategoryTheory Opposite TopologicalSpace

/--
[TopCat_Sheaf_isIso_of_isIso_app_of_isBasis](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_TopCat_Sheaf_isIso_of_isIso_app_of_isBasis.lean)
-/
@[main]
private lemma main
  {C : Type u} [Category.{v} C]
  {X : TopCat.{w}}
  {ι : Type u'}
  {B : ι → Opens X}
  {F G : TopCat.Sheaf C X}
  {φ : F ⟶ G}
-- given
  (hB : Opens.IsBasis (Set.range B))
  (h : ∀ i, IsIso (φ.1.app (op (B i)))) :
-- imply
  IsIso φ := by
-- proof
  haveI := TopCat.Opens.coverDense_inducedFunctor hB
  haveI : IsIso (Functor.whiskerLeft (inducedFunctor B).op φ.1) := by
    refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
    intro i
    exact h i.unop
  exact Functor.IsCoverDense.iso_of_restrict_iso φ this


-- created on 2026-10-05
