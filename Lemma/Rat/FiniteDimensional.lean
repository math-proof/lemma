import Mathlib
import sympy.Basic

open CategoryTheory Module groupCohomology

/--
[groupCohomology_finiteDimensional_H1_of_finite](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_groupCohomology_finiteDimensional_H1_of_finite.lean)
-/
@[main]
private lemma main
  [Field k] [Group G] [Finite G]
  {A : Rep k G} [FiniteDimensional k A] :
-- imply
  FiniteDimensional k (H1 A) := by
-- proof
  have : FiniteDimensional k (G → A) := Module.Finite.pi
  have : FiniteDimensional k (cocycles₁ A) := FiniteDimensional.finiteDimensional_submodule _
  exact Module.Finite.of_surjective (ModuleCat.Hom.hom (H1π A))
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)


-- created on 2026-10-03
