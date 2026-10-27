import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeComponent
open StatMech StatMech.Onsager


/--
[ons_decorated_split_cycle_at_external](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEdgeComponent.lean)
-/
@[path]
private lemma ons_decorated_split_cycle_at_external_eq
  {L : ℕ}
  [Fact (2 < L)]
  {D : ons_DecoratedEvenSubgraph L}
  {d : ons_Dart L}
-- given
  (hd : s(d, ons_dartRev L d) ∈ D.1) :
-- imply
  ∃ (q : (ons_decGraph L).Walk d d) (R : ons_DecoratedEvenSubgraph L), q.IsCycle ∧ q.snd = ons_dartRev L d ∧ D.1 = q.edges.toFinset ∪ R.1 ∧ Disjoint q.edges.toFinset R.1 ∧ (∀ v ∈ q.support, incCount R.1 v = 0) ∧ incCount R.1 d = 0 ∧ incCount R.1 (ons_dartRev L d) = 0 := by
-- proof
  apply StatMech.Onsager.ons_decorated_split_cycle_at_external L D d hd

/--
[ons_cycle_vertices_disjoint_of_incCount_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEdgeComponent.lean)
-/
@[path]
private lemma ons_cycle_vertices_disjoint_of_incCount_zero_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {u v : V}
  {q : G.Walk u u}
  {p : G.Walk v v}
  {F : Finset (Sym2 V)}
-- given
  (hp : p.IsCycle)
  (hzero : ∀ w ∈ q.support, incCount F w = 0)
  (hpF : p.edges.toFinset ⊆ F) :
-- imply
  Disjoint q.toSubgraph.verts p.toSubgraph.verts := by
-- proof
  apply StatMech.Onsager.ons_cycle_vertices_disjoint_of_incCount_zero G q p hp F hzero hpF

/--
[ons_originalEdgesOfDecorated_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEdgeComponent.lean)
-/
@[path]
private lemma ons_originalEdgesOfDecorated_split_eq
  {L : ℕ}
  [Fact (2 < L)]
  {D R : ons_DecoratedEvenSubgraph L}
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hsplit : D.1 = q.edges.toFinset ∪ R.1) :
-- imply
  ons_originalEdgesOfDecorated L D = ons_walkOriginalEdges q ∪ ons_originalEdgesOfDecorated L R := by
-- proof
  apply StatMech.Onsager.ons_originalEdgesOfDecorated_split L D R q hsplit

/--
[ons_originalEdgesOfDecorated_split_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEdgeComponent.lean)
-/
@[path]
private lemma ons_originalEdgesOfDecorated_split_disjoint_eq
  {L : ℕ}
  [Fact (2 < L)]
  {R : ons_DecoratedEvenSubgraph L}
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hdisj : Disjoint q.edges.toFinset R.1) :
-- imply
  Disjoint (ons_walkOriginalEdges q) (ons_originalEdgesOfDecorated L R) := by
-- proof
  apply StatMech.Onsager.ons_originalEdgesOfDecorated_split_disjoint L R q hdisj

/--
[ons_originalHomology_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEdgeComponent.lean)
-/
@[path]
private lemma ons_originalHomology_split_eq
  {L : ℕ}
  [Fact (2 < L)]
  {D R : ons_DecoratedEvenSubgraph L}
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
-- given
  (hsplit : D.1 = q.edges.toFinset ∪ R.1)
  (hdisj : Disjoint q.edges.toFinset R.1) :
-- imply
  ons_evenHomology L (ons_originalEdgesOfDecorated L D) = ons_evenHomology L (ons_walkOriginalEdges q) + ons_evenHomology L (ons_originalEdgesOfDecorated L R) := by
-- proof
  apply StatMech.Onsager.ons_originalHomology_split L D R q hsplit hdisj

/--
[ons_originalWeight_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEdgeComponent.lean)
-/
@[path]
private lemma ons_originalWeight_split_eq
  {L : ℕ}
  [Fact (2 < L)]
  {D R : ons_DecoratedEvenSubgraph L}
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
-- given
  (hsplit : D.1 = q.edges.toFinset ∪ R.1)
  (hdisj : Disjoint q.edges.toFinset R.1) :
-- imply
  (∏ edge ∈ ons_originalEdgesOfDecorated L D, weight edge) = (∏ edge ∈ ons_walkOriginalEdges q, weight edge) * ∏ edge ∈ ons_originalEdgesOfDecorated L R, weight edge := by
-- proof
  apply StatMech.Onsager.ons_originalWeight_split L D R q hsplit hdisj weight

/--
[ons_decoratedWeightedSpinWeight_split_of_isotropic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEdgeComponent.lean)
-/
@[path]
private lemma ons_decoratedWeightedSpinWeight_split_of_isotropic_eq
  {L : ℕ}
  [Fact (2 < L)]
  {D R : ons_DecoratedEvenSubgraph L}
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {a b : Fin 2}
-- given
  (hsplit : D.1 = q.edges.toFinset ∪ R.1)
  (hdisj : Disjoint q.edges.toFinset R.1)
  (hisotropic : ons_homologyIntersection (ons_evenHomology L (ons_walkOriginalEdges q)) (ons_evenHomology L (ons_originalEdgesOfDecorated L R)) = 0) :
-- imply
  ons_decoratedWeightedSpinWeight L weight a b D = ((ons_spinCharacter a b (ons_evenHomology L (ons_walkOriginalEdges q)) : ℂ) * ∏ edge ∈ ons_walkOriginalEdges q, weight edge) * ons_decoratedWeightedSpinWeight L weight a b R := by
-- proof
  apply StatMech.Onsager.ons_decoratedWeightedSpinWeight_split_of_isotropic L D R q hsplit hdisj weight a b hisotropic


-- created on 2026-10-23
