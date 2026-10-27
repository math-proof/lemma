import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.GroupCohomology.TateCohomology
import Lemma.Representation.EqIndBotMk
import Lemma.Int.P2MUtil

open CategoryTheory Rep

/--
[Rep_indBotPi_indBotMk](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Rep_indBotPi_indBotMk.lean)
-/
@[path]
private lemma main
  {k G : Type u} [CommRing k] [Group G]
  {A : Rep.{u} k G}
  {g : G}
  {a : A} :
-- imply
  (Rep.indBotπ A).hom (A.indBotMk g a) = A.ρ g⁻¹ a := by
-- proof
  simp [Rep.indBotπ, Rep.indBotMk, Rep.indResHomEquiv]


-- created on 2026-10-23
