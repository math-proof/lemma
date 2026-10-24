import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_GroupCohomology_LocallyConstantClasses
open CategoryTheory Module groupCohomology


/-- ported from external source -/
@[path]
private lemma main
  {k G : Type u} [Field k] [Group G]
  {S : Subgroup G} [S.Normal]
  {A : Rep k G} :
-- imply
  finrank k (inflationImage A S) = finrank k (H1 (A.quotientToInvariants S)) :=
-- proof
  LinearMap.finrank_range_of_inj
    ((ModuleCat.mono_iff_injective _).1 (inferInstance : Mono (H1InfRes A S).f))


-- created on 2026-10-23
