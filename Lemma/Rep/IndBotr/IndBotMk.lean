import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_GroupCohomology_TateCohomology
import Lemma.Definitions.Def_GroupCohomology_TateDimensionShift
import Lemma.Int.P2MUtil

open CategoryTheory Rep

/--
[Rep_indBotr_indBotMk](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Rep_indBotr_indBotMk.lean)
-/
@[path]
private lemma main
  {k G : Type u} [CommRing k] [Group G]
  {A : Rep.{u} k G}
  {g : G}
  {a : A} :
-- imply
  A.indBotr (A.indBotMk g a) = (Finsupp.single g (1 : k)) 1 • a := by
-- proof
  simp [Rep.indBotr, Rep.indBotMk]


-- created on 2026-10-23
