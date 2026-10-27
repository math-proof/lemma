import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.MedialPathCycleSplice
open SimpleGraph Set StatMech StatMech.Universality


/--
[walkCycleArcSplice_of_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MedialPathCycleSplice.lean)
-/
@[path]
private lemma walkCycleArcSplice_of_order_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {u v a b c d : V}
  {p : G.Walk u v}
  {r : (G.deleteEdges {s(a, b), s(c, d)}).Walk d c}
-- given
  (hp : p.IsPath)
  (ha : a ∈ p.support)
  (hb : b ∈ p.support)
  (hab : p.support.idxOf a < p.support.idxOf b)
  (hr : r.IsPath)
  (hd : d ∈ r.support)
  (hc : c ∈ r.support)
  (hdisjoint : p.support.Disjoint r.support) :
-- imply
  ∃ q : (medialTwoEdgeSwitch G a b c d).Walk u v, q.IsPath ∧ q.support = p.support.take (p.support.idxOf a + 1) ++ r.support ++ p.support.drop (p.support.idxOf b) := by
-- proof
  apply StatMech.Universality.walkCycleArcSplice_of_order G p hp ha hb hab r hr hd hc hdisjoint


-- created on 2026-10-23
