import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.DecorationCoefficientAssembly
open StatMech StatMech.Onsager


/--
[ons_decCycle_remainder_originalHomology_isotropic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCoefficientAssembly.lean)
-/
@[path]
private lemma ons_decCycle_remainder_originalHomology_isotropic_eq
  {L : ℕ}
  [Fact (2 < L)]
  {d : ons_Dart L}
  {q : (ons_decGraph L).Walk d d}
  {R : ons_DecoratedEvenSubgraph L}
-- given
  (hq : q.IsCycle)
  (hzero : ∀ v ∈ q.support, incCount R.1 v = 0) :
-- imply
  ons_homologyIntersection (ons_evenHomology L (ons_walkOriginalEdges q)) (ons_evenHomology L (ons_originalEdgesOfDecorated L R)) = 0 := by
-- proof
  apply StatMech.Onsager.ons_decCycle_remainder_originalHomology_isotropic L q hq R hzero

/--
[ons_decoratedWeightedSpinWeight_split_eq_neg_cycleWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCoefficientAssembly.lean)
-/
@[path]
private lemma ons_decoratedWeightedSpinWeight_split_eq_neg_cycleWeight_eq
  {L : ℕ}
  [Fact (2 < L)]
  {D : ons_DecoratedEvenSubgraph L}
  {d : ons_Dart L}
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {a b : Fin 2}
-- given
  (hd : s(d, ons_dartRev L d) ∈ D.1) :
-- imply
  ∃ (q : (ons_decGraph L).Walk d d) (R : ons_DecoratedEvenSubgraph L), q.IsCycle ∧ q.snd = ons_dartRev L d ∧ D.1 = q.edges.toFinset ∪ R.1 ∧ Disjoint q.edges.toFinset R.1 ∧ (∀ v ∈ q.support, incCount R.1 v = 0) ∧ incCount R.1 d = 0 ∧ incCount R.1 (ons_dartRev L d) = 0 ∧ ons_decoratedWeightedSpinWeight L weight a b D = -ons_edgeWeight (ons_KWmatWeightedPhase L weight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) (ons_decCycleFirstReturn q) * ons_decoratedWeightedSpinWeight L weight a b R := by
-- proof
  apply StatMech.Onsager.ons_decoratedWeightedSpinWeight_split_eq_neg_cycleWeight L D d hd weight a b

/--
[ons_weightedSpinEdgeCoefficient_eq_decoratedCycleSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCoefficientAssembly.lean)
-/
@[path]
private lemma ons_weightedSpinEdgeCoefficient_eq_decoratedCycleSplit_eq
  {L : ℕ}
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {a b : Fin 2}
  {d : ons_Dart L} :
-- imply
  ons_weightedSpinEdgeCoefficient L weight a b (ons_portEdge L d) = ∑ D : ons_DecoratedContainingEdge L d, -ons_edgeWeight (ons_KWmatWeightedPhase L weight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)) (ons_decCycleFirstReturn (ons_decoratedEdgeSplit L d D).cycle) * ons_decoratedWeightedSpinWeight L weight a b (ons_decoratedEdgeSplit L d D).remainder := by
-- proof
  apply StatMech.Onsager.ons_weightedSpinEdgeCoefficient_eq_decoratedCycleSplit L weight a b d

/--
[ons_weightedEdgeCoefficientIdentity_of_decoratedCycleRemoval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationCoefficientAssembly.lean)
-/
@[path]
private lemma ons_weightedEdgeCoefficientIdentity_of_decoratedCycleRemoval_eq
  {L : ℕ}
  [Fact (2 < L)]
-- given
  (hremove : ons_decoratedCycleRemovalIdentity L) :
-- imply
  ons_weightedEdgeCoefficientIdentity L := by
-- proof
  apply StatMech.Onsager.ons_weightedEdgeCoefficientIdentity_of_decoratedCycleRemoval L hremove


-- created on 2026-10-23
