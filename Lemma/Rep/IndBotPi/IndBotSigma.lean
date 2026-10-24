import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_GroupCohomology_TateCohomology
import Lemma.Definitions.Def_GroupCohomology_TateDimensionShift
import Lemma.Int.P2MUtil

open CategoryTheory Rep

/--
[Rep_indBotPi_indBotSigma](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Rep_indBotPi_indBotSigma.lean)
-/
@[path]
private lemma main
  {k G : Type u} [CommRing k] [Group G]
  {A : Rep.{u} k G}
  {a : A} :
-- imply
  (Rep.indBotπ A).hom (A.indBotσ a) = a := by
-- proof
  show (Rep.indBotπ A).hom (A.indBotMk 1 a) = a
  simp [Rep.indBotπ, Rep.indBotMk, Rep.indResHomEquiv]


-- created on 2026-10-23
