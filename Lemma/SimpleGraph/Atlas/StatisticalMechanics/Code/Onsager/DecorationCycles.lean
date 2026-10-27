import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.DecorationCycles
open StatMech StatMech.Onsager


/--
[ons_originalEdgesOfDecorated_eq_empty_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCycles.lean)
-/
@[path]
private lemma ons_originalEdgesOfDecorated_eq_empty_iff_eq
  {L : ℕ}
  [Fact (2 < L)]
  {D : ons_DecoratedEvenSubgraph L} :
-- imply
  ons_originalEdgesOfDecorated L D = ∅ ↔ D.1 = ∅ := by
-- proof
  apply StatMech.Onsager.ons_originalEdgesOfDecorated_eq_empty_iff L D

/--
[ons_decoratedExternalEdges_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCycles.lean)
-/
@[path]
private lemma ons_decoratedExternalEdges_nonempty_eq
  {L : ℕ}
  [Fact (2 < L)]
  {D : ons_DecoratedEvenSubgraph L}
-- given
  (hD : D.1.Nonempty) :
-- imply
  (ons_decoratedExternalEdges D.1).Nonempty := by
-- proof
  apply StatMech.Onsager.ons_decoratedExternalEdges_nonempty L D hD

/--
[ons_decCycle_exists_external](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCycles.lean)
-/
@[path]
private lemma ons_decCycle_exists_external_eq
  {L : ℕ}
  [Fact (2 < L)]
  {v : ons_Dart L}
  {p : (ons_decGraph L).Walk v v}
-- given
  (hp : p.IsCycle) :
-- imply
  ∃ d : ons_Dart L, s(d, ons_dartRev L d) ∈ p.edges.toFinset := by
-- proof
  apply StatMech.Onsager.ons_decCycle_exists_external p hp

/--
[ons_decCycle_root_at_external](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCycles.lean)
-/
@[path]
private lemma ons_decCycle_root_at_external_eq
  {L : ℕ}
  [Fact (2 < L)]
  {v : ons_Dart L}
  {p : (ons_decGraph L).Walk v v}
  {d : ons_Dart L}
-- given
  (hp : p.IsCycle)
  (hd : s(d, ons_dartRev L d) ∈ p.edges.toFinset) :
-- imply
  ∃ q : (ons_decGraph L).Walk d d, q.IsCycle ∧ q.snd = ons_dartRev L d ∧ q.edges.toFinset = p.edges.toFinset := by
-- proof
  apply StatMech.Onsager.ons_decCycle_root_at_external p hp d hd

/--
[ons_decCycle_root_external](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCycles.lean)
-/
@[path]
private lemma ons_decCycle_root_external_eq
  {L : ℕ}
  [Fact (2 < L)]
  {v : ons_Dart L}
  {p : (ons_decGraph L).Walk v v}
-- given
  (hp : p.IsCycle) :
-- imply
  ∃ (d : ons_Dart L) (q : (ons_decGraph L).Walk d d), q.IsCycle ∧ q.snd = ons_dartRev L d ∧ q.edges.toFinset = p.edges.toFinset := by
-- proof
  apply StatMech.Onsager.ons_decCycle_root_external p hp


-- created on 2026-10-23
