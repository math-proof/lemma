import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.DecorationWeighted
open StatMech StatMech.Onsager


/--
[ons_weightedSpinCharacterSum_eq_decorated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWeighted.lean)
-/
@[path]
private lemma ons_weightedSpinCharacterSum_eq_decorated_eq
  {L : ℕ}
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {a b : Fin 2} :
-- imply
  ons_weightedSpinCharacterSum L weight a b = ∑ D : ons_DecoratedEvenSubgraph L, ons_decoratedWeightedSpinWeight L weight a b D := by
-- proof
  apply StatMech.Onsager.ons_weightedSpinCharacterSum_eq_decorated L weight a b

/--
[ons_portEdge_mem_originalEdgesOfDecorated_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWeighted.lean)
-/
@[path]
private lemma ons_portEdge_mem_originalEdgesOfDecorated_iff_eq
  {L : ℕ}
  [Fact (2 < L)]
  {D : ons_DecoratedEvenSubgraph L}
  {e : ons_Dart L} :
-- imply
  ons_portEdge L e ∈ ons_originalEdgesOfDecorated L D ↔ s(e, ons_dartRev L e) ∈ D.1 := by
-- proof
  apply StatMech.Onsager.ons_portEdge_mem_originalEdgesOfDecorated_iff L D e

/--
[ons_weightedSpinEdgeCoefficient_eq_decorated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWeighted.lean)
-/
@[path]
private lemma ons_weightedSpinEdgeCoefficient_eq_decorated_eq
  {L : ℕ}
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {a b : Fin 2}
  {e : ons_Dart L} :
-- imply
  ons_weightedSpinEdgeCoefficient L weight a b (ons_portEdge L e) = ∑ D : ons_DecoratedEvenSubgraph L, if s(e, ons_dartRev L e) ∈ D.1 then ons_decoratedWeightedSpinWeight L weight a b D else 0 := by
-- proof
  apply StatMech.Onsager.ons_weightedSpinEdgeCoefficient_eq_decorated L weight a b e

/--
[ons_decoratedOriginalWeight_biUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWeighted.lean)
-/
@[path]
private lemma ons_decoratedOriginalWeight_biUnion_eq
  {L : ℕ}
  [Fact (2 < L)]
  {iota : Type}
  [Fintype iota]
  [DecidableEq iota]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {D : ons_DecoratedEvenSubgraph L}
  {piece : iota → Finset (Sym2 (ons_Dart L))}
-- given
  (hcover : D.1 = Finset.univ.biUnion piece)
  (hdisj : ((Finset.univ : Finset iota) : Set iota).PairwiseDisjoint piece) :
-- imply
  (∏ edge ∈ ons_originalEdgesOfDecorated L D, weight edge) = ∏ i, ∏ edge ∈ (ons_decoratedExternalEdges (piece i)).image ons_decEdgeProjection, weight edge := by
-- proof
  apply StatMech.Onsager.ons_decoratedOriginalWeight_biUnion weight D piece hcover hdisj

/--
[ons_decoratedWeightedSpinWeight_factor_of_isotropic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWeighted.lean)
-/
@[path]
private lemma ons_decoratedWeightedSpinWeight_factor_of_isotropic_eq
  {L : ℕ}
  [Fact (2 < L)]
  {iota : Type}
  [Fintype iota]
  [DecidableEq iota]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {a b : Fin 2}
  {D : ons_DecoratedEvenSubgraph L}
  {piece : iota → Finset (Sym2 (ons_Dart L))}
-- given
  (hcover : D.1 = Finset.univ.biUnion piece)
  (hdisj : ((Finset.univ : Finset iota) : Set iota).PairwiseDisjoint piece)
  (hisotropic : ∀ i j, i ≠ j → ons_homologyIntersection (ons_evenHomology L ((ons_decoratedExternalEdges (piece i)).image ons_decEdgeProjection)) (ons_evenHomology L ((ons_decoratedExternalEdges (piece j)).image ons_decEdgeProjection)) = 0) :
-- imply
  ons_decoratedWeightedSpinWeight L weight a b D = ∏ i, (ons_spinCharacter a b (ons_evenHomology L ((ons_decoratedExternalEdges (piece i)).image ons_decEdgeProjection)) : ℂ) * ∏ edge ∈ (ons_decoratedExternalEdges (piece i)).image ons_decEdgeProjection, weight edge := by
-- proof
  apply StatMech.Onsager.ons_decoratedWeightedSpinWeight_factor_of_isotropic weight a b D piece hcover hdisj hisotropic

/--
[ons_decoratedWeightedSpinTerm_cycle_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationWeighted.lean)
-/
@[path]
private lemma ons_decoratedWeightedSpinTerm_cycle_data_eq
  {L : ℕ}
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → ℂ}
  {D : ons_DecoratedEvenSubgraph L} :
-- imply
  ∃ (iota : Type) (_ : Fintype iota) (_ : DecidableEq iota) (base : iota → ons_Dart L) (p : (i : iota) → (ons_decGraph L).Walk (base i) (base i)), (∀ i, (p i).IsCycle) ∧ D.1 = Finset.univ.biUnion (fun i => (p i).edges.toFinset) ∧ ((Finset.univ : Finset iota) : Set iota).PairwiseDisjoint (fun i => (p i).edges.toFinset) ∧ ((Finset.univ : Finset iota) : Set iota).PairwiseDisjoint (fun i => (p i).toSubgraph.verts) ∧ (∏ edge ∈ ons_originalEdgesOfDecorated L D, weight edge) = ∏ i, ∏ edge ∈ ons_walkOriginalEdges (p i), weight edge := by
-- proof
  apply StatMech.Onsager.ons_decoratedWeightedSpinTerm_cycle_data L weight D


-- created on 2026-10-23
