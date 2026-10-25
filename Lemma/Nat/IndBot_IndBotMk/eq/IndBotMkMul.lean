import Mathlib
import sympy.Basic
import Lemma.GroupCohomology.TateCohomology
import Lemma.Representation.EqIndBotMk
open CategoryTheory Rep


/-- ported from external source -/
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
