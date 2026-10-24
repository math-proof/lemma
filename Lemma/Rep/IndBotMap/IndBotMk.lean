import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_GroupCohomology_TateCohomology
import Lemma.Definitions.Def_GroupCohomology_TateDimensionShift
import Lemma.Definitions.Def_GroupCohomology_TateDimensionShiftMaps
import Lemma.Int.P2MUtil

open CategoryTheory Rep CategoryTheory.MonoidalCategory

/--
[Rep_indBotMap_indBotMk](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Rep_indBotMap_indBotMk.lean)
-/
@[path]
private lemma main
  {k G : Type u} [CommRing k] [Group G]
  {A B : Rep.{u} k G}
  {φ : A ⟶ B}
  {g : G}
  {a : A} :
-- imply
  (Rep.indBotMap φ).hom (A.indBotMk g a) = B.indBotMk g (φ.hom a) := by
-- proof
  rfl


-- created on 2026-10-23
