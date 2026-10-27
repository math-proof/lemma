import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.GroupCohomology.TateCohomology
import Lemma.Representation.EqIndBotMk
open CategoryTheory Rep


/-- ported from external source -/
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
