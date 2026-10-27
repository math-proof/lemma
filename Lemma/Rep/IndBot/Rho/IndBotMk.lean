import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.GroupCohomology.TateCohomology
import Lemma.Representation.EqIndBotMk
import Lemma.Int.P2MUtil

open CategoryTheory Rep

/--
[Rep_indBot_rho_indBotMk](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Rep_indBot_rho_indBotMk.lean)
-/
@[path]
private lemma main
  {k G : Type u} [CommRing k] [Group G]
  {A : Rep.{u} k G}
  {g h : G}
  {a : A} :
-- imply
  A.indBot.ρ g (A.indBotMk h a) = A.indBotMk (h * g⁻¹) a :=
-- proof
  Representation.ind_mk _ _ g h a


-- created on 2026-10-23
