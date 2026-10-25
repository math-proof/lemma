import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.DecorationSum.Part4
open StatMech StatMech.Onsager


/--
[ons_originalEdgesOfDecorated_eq_portPatternEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSum.lean)
-/
@[path]
private lemma ons_originalEdgesOfDecorated_eq_portPatternEdges_eq
  {L : ℕ}
  [Fact (2 < L)]
  {D : ons_DecoratedEvenSubgraph L} :
-- imply
  ons_originalEdgesOfDecorated L D = ons_portPatternEdges L (ons_portPatternOfDecorated L D.1 D.2) := by
-- proof
  apply StatMech.Onsager.ons_originalEdgesOfDecorated_eq_portPatternEdges L D

/--
[ons_originalEdgesOfDecorated_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSum.lean)
-/
@[path]
private lemma ons_originalEdgesOfDecorated_even_eq
  {L : ℕ}
  [Fact (2 < L)]
  {D : ons_DecoratedEvenSubgraph L} :
-- imply
  ons_originalEdgesOfDecorated L D ∈ evenSubgraphs (onsTorusGraph L) := by
-- proof
  apply StatMech.Onsager.ons_originalEdgesOfDecorated_even L D

/--
[ons_decEdgeProjection_external](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSum.lean)
-/
@[path]
private lemma ons_decEdgeProjection_external_eq
  {L : ℕ}
  {d : ons_Dart L} :
-- imply
  ons_decEdgeProjection s(d, ons_dartRev L d) = ons_portEdge L d := by
-- proof
  apply StatMech.Onsager.ons_decEdgeProjection_external L d

/--
[ons_decEdgeProjection_injective_of_external](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSum.lean)
-/
@[path]
private lemma ons_decEdgeProjection_injective_of_external_eq
  {L : ℕ}
  [Fact (2 < L)]
  {edge edge' : Sym2 (ons_Dart L)}
-- given
  (he : ons_decIsExternal edge)
  (he' : ons_decIsExternal edge')
  (hproj : ons_decEdgeProjection edge = ons_decEdgeProjection edge') :
-- imply
  edge = edge' := by
-- proof
  apply StatMech.Onsager.ons_decEdgeProjection_injective_of_external L he he' hproj

/--
[ons_decoratedExternalEdges_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSum.lean)
-/
@[path]
private lemma ons_decoratedExternalEdges_image_eq
  {L : ℕ}
  [Fact (2 < L)]
  {D : ons_DecoratedEvenSubgraph L} :
-- imply
  (ons_decoratedExternalEdges D.1).image ons_decEdgeProjection = ons_originalEdgesOfDecorated L D := by
-- proof
  apply StatMech.Onsager.ons_decoratedExternalEdges_image L D

/--
[ons_originalEdgesOfDecorated_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSum.lean)
-/
@[path]
private lemma ons_originalEdgesOfDecorated_card_eq
  {L : ℕ}
  [Fact (2 < L)]
  {D : ons_DecoratedEvenSubgraph L} :
-- imply
  (ons_originalEdgesOfDecorated L D).card = (ons_decoratedExternalEdges D.1).card := by
-- proof
  apply StatMech.Onsager.ons_originalEdgesOfDecorated_card L D

/--
[ons_decoratedSpinWeight_eq_external](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSum.lean)
-/
@[path]
private lemma ons_decoratedSpinWeight_eq_external_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x : ℝ}
  {a b : Fin 2}
  {D : ons_DecoratedEvenSubgraph L} :
-- imply
  ons_decoratedSpinWeight L x a b D = ons_spinCharacter a b (ons_evenHomology L (ons_originalEdgesOfDecorated L D)) * x ^ (ons_decoratedExternalEdges D.1).card := by
-- proof
  apply StatMech.Onsager.ons_decoratedSpinWeight_eq_external L x a b D

/--
[ons_walkOriginalEdges_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSum.lean)
-/
@[path]
private lemma ons_walkOriginalEdges_even_eq
  {L : ℕ}
  [Fact (2 < L)]
  {v : ons_Dart L}
  {p : (ons_decGraph L).Walk v v}
-- given
  (hp : p.IsCycle) :
-- imply
  ons_walkOriginalEdges p ∈ evenSubgraphs (onsTorusGraph L) := by
-- proof
  apply StatMech.Onsager.ons_walkOriginalEdges_even p hp

/--
[ons_decoratedExternalEdges_card_biUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSum.lean)
-/
@[path]
private lemma ons_decoratedExternalEdges_card_biUnion_eq
  {L : ℕ}
  [Fact (2 < L)]
  {iota : Type}
  [Fintype iota]
  [DecidableEq iota]
  {D : Finset (Sym2 (ons_Dart L))}
  {piece : iota → Finset (Sym2 (ons_Dart L))}
-- given
  (hcover : D = Finset.univ.biUnion piece)
  (hdisj : ((Finset.univ : Finset iota) : Set iota).PairwiseDisjoint piece) :
-- imply
  (ons_decoratedExternalEdges D).card = ∑ i, (ons_decoratedExternalEdges (piece i)).card := by
-- proof
  apply StatMech.Onsager.ons_decoratedExternalEdges_card_biUnion D piece hcover hdisj

/--
[ons_decoratedExternal_pow_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSum.lean)
-/
@[path]
private lemma ons_decoratedExternal_pow_factor_eq
  {L : ℕ}
  [Fact (2 < L)]
  {iota : Type}
  [Fintype iota]
  [DecidableEq iota]
  {x : ℝ}
  {D : Finset (Sym2 (ons_Dart L))}
  {piece : iota → Finset (Sym2 (ons_Dart L))}
-- given
  (hcover : D = Finset.univ.biUnion piece)
  (hdisj : ((Finset.univ : Finset iota) : Set iota).PairwiseDisjoint piece) :
-- imply
  x ^ (ons_decoratedExternalEdges D).card = ∏ i, x ^ (ons_decoratedExternalEdges (piece i)).card := by
-- proof
  apply StatMech.Onsager.ons_decoratedExternal_pow_factor x D piece hcover hdisj

/--
[ons_originalHomology_biUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSum.lean)
-/
@[path]
private lemma ons_originalHomology_biUnion_eq
  {L : ℕ}
  [Fact (2 < L)]
  {iota : Type}
  [Fintype iota]
  [DecidableEq iota]
  {D : ons_DecoratedEvenSubgraph L}
  {piece : iota → Finset (Sym2 (ons_Dart L))}
-- given
  (hcover : D.1 = Finset.univ.biUnion piece)
  (hdisj : ((Finset.univ : Finset iota) : Set iota).PairwiseDisjoint piece) :
-- imply
  ons_evenHomology L (ons_originalEdgesOfDecorated L D) = ∑ i, ons_evenHomology L ((ons_decoratedExternalEdges (piece i)).image ons_decEdgeProjection) := by
-- proof
  apply StatMech.Onsager.ons_originalHomology_biUnion D piece hcover hdisj

/--
[ons_decoratedSpinWeight_factor_of_isotropic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSum.lean)
-/
@[path]
private lemma ons_decoratedSpinWeight_factor_of_isotropic_eq
  {L : ℕ}
  [Fact (2 < L)]
  {iota : Type}
  [Fintype iota]
  [DecidableEq iota]
  {x : ℝ}
  {a b : Fin 2}
  {D : ons_DecoratedEvenSubgraph L}
  {piece : iota → Finset (Sym2 (ons_Dart L))}
-- given
  (hcover : D.1 = Finset.univ.biUnion piece)
  (hdisj : ((Finset.univ : Finset iota) : Set iota).PairwiseDisjoint piece)
  (hisotropic : ∀ i j, i ≠ j → ons_homologyIntersection (ons_evenHomology L ((ons_decoratedExternalEdges (piece i)).image ons_decEdgeProjection)) (ons_evenHomology L ((ons_decoratedExternalEdges (piece j)).image ons_decEdgeProjection)) = 0) :
-- imply
  ons_decoratedSpinWeight L x a b D = ∏ i, ons_spinCharacter a b (ons_evenHomology L ((ons_decoratedExternalEdges (piece i)).image ons_decEdgeProjection)) * x ^ (ons_decoratedExternalEdges (piece i)).card := by
-- proof
  apply StatMech.Onsager.ons_decoratedSpinWeight_factor_of_isotropic x a b D piece hcover hdisj hisotropic

/--
[ons_spinCharacterSum_eq_decorated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSum.lean)
-/
@[path]
private lemma ons_spinCharacterSum_eq_decorated_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x : ℝ}
  {a b : Fin 2} :
-- imply
  ons_spinCharacterSum L x a b = ∑ D : ons_DecoratedEvenSubgraph L, ons_decoratedSpinWeight L x a b D := by
-- proof
  apply StatMech.Onsager.ons_spinCharacterSum_eq_decorated L x a b

/--
[ons_decoratedSpinTerm_cycle_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSum.lean)
-/
@[path]
private lemma ons_decoratedSpinTerm_cycle_decomposition_eq
  {L : ℕ}
  [Fact (2 < L)]
  {D : ons_DecoratedEvenSubgraph L} :
-- imply
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (base : ι → ons_Dart L) (p : (i : ι) → (ons_decGraph L).Walk (base i) (base i)), (∀ i, (p i).IsCycle) ∧ D.1 = Finset.univ.biUnion (fun i => (p i).edges.toFinset) ∧ ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint (fun i => (p i).edges.toFinset) ∧ ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint (fun i => (p i).toSubgraph.verts) := by
-- proof
  apply StatMech.Onsager.ons_decoratedSpinTerm_cycle_decomposition L D

/--
[ons_decoratedSpinTerm_cycle_weight_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSum.lean)
-/
@[path]
private lemma ons_decoratedSpinTerm_cycle_weight_factor_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x : ℝ}
  {D : ons_DecoratedEvenSubgraph L} :
-- imply
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (base : ι → ons_Dart L) (p : (i : ι) → (ons_decGraph L).Walk (base i) (base i)), (∀ i, (p i).IsCycle) ∧ D.1 = Finset.univ.biUnion (fun i => (p i).edges.toFinset) ∧ ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint (fun i => (p i).edges.toFinset) ∧ ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint (fun i => (p i).toSubgraph.verts) ∧ x ^ (ons_originalEdgesOfDecorated L D).card = ∏ i, x ^ (ons_walkExternalEdges (p i)).card := by
-- proof
  apply StatMech.Onsager.ons_decoratedSpinTerm_cycle_weight_factor L x D

/--
[ons_decoratedSpinTerm_cycle_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSum.lean)
-/
@[path]
private lemma ons_decoratedSpinTerm_cycle_data_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x : ℝ}
  {D : ons_DecoratedEvenSubgraph L} :
-- imply
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (base : ι → ons_Dart L) (p : (i : ι) → (ons_decGraph L).Walk (base i) (base i)), (∀ i, (p i).IsCycle) ∧ D.1 = Finset.univ.biUnion (fun i => (p i).edges.toFinset) ∧ ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint (fun i => (p i).edges.toFinset) ∧ ((Finset.univ : Finset ι) : Set ι).PairwiseDisjoint (fun i => (p i).toSubgraph.verts) ∧ x ^ (ons_originalEdgesOfDecorated L D).card = ∏ i, x ^ (ons_walkExternalEdges (p i)).card ∧ ons_evenHomology L (ons_originalEdgesOfDecorated L D) = ∑ i, ons_evenHomology L (ons_walkOriginalEdges (p i)) := by
-- proof
  apply StatMech.Onsager.ons_decoratedSpinTerm_cycle_data L x D


-- created on 2026-10-23
