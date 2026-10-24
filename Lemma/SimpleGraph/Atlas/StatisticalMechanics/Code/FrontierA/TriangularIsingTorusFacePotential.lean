import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFacePotential
open StatMech StatMech.FrontierA


/--
[triangularTorusPositiveDirection_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean)
-/
@[path]
private lemma triangularTorusPositiveDirection_injective_eq :
-- imply
  Function.Injective triangularTorusPositiveDirection := by
-- proof
  apply StatMech.FrontierA.triangularTorusPositiveDirection_injective

/--
[triangularTorusPositiveEdge_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean)
-/
@[path]
private lemma triangularTorusPositiveEdge_eq_iff_eq
  {L : Nat}
  [Fact (2 < L)]
  {p q : ZMod L × ZMod L}
  {a b : Fin 3} :
-- imply
  (triangularTorusDartEquiv L (p, triangularTorusPositiveDirection a)).edge = (triangularTorusDartEquiv L (q, triangularTorusPositiveDirection b)).edge ↔ p = q ∧ a = b := by
-- proof
  apply StatMech.FrontierA.triangularTorusPositiveEdge_eq_iff L p q a b

/--
[triangularTorusEastEdge_eq_ons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean)
-/
@[path]
private lemma triangularTorusEastEdge_eq_ons_eq
  {L : Nat}
  [Fact (2 < L)]
  {p : ZMod L × ZMod L} :
-- imply
  triangularTorusEastEdge L p = ons_portEdge L (p, 0) := by
-- proof
  apply StatMech.FrontierA.triangularTorusEastEdge_eq_ons L p

/--
[triangularTorusNorthEdge_eq_ons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean)
-/
@[path]
private lemma triangularTorusNorthEdge_eq_ons_eq
  {L : Nat}
  [Fact (2 < L)]
  {p : ZMod L × ZMod L} :
-- imply
  triangularTorusNorthEdge L p = ons_portEdge L (p, 1) := by
-- proof
  apply StatMech.FrontierA.triangularTorusNorthEdge_eq_ons L p

/--
[ons_eastPortEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean)
-/
@[path]
private lemma ons_eastPortEdge_injective_eq
  {L : Nat}
  [Fact (2 < L)] :
-- imply
  Function.Injective (fun p : ZMod L × ZMod L => ons_portEdge L (p, 0)) := by
-- proof
  apply StatMech.FrontierA.ons_eastPortEdge_injective L

/--
[ons_northPortEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean)
-/
@[path]
private lemma ons_northPortEdge_injective_eq
  {L : Nat}
  [Fact (2 < L)] :
-- imply
  Function.Injective (fun p : ZMod L × ZMod L => ons_portEdge L (p, 1)) := by
-- proof
  apply StatMech.FrontierA.ons_northPortEdge_injective L

/--
[ons_eastPortEdge_ne_northPortEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean)
-/
@[path]
private lemma ons_eastPortEdge_ne_northPortEdge_eq
  {L : Nat}
  [Fact (2 < L)]
  {p q : ZMod L × ZMod L} :
-- imply
  ons_portEdge L (p, 0) ≠ ons_portEdge L (q, 1) := by
-- proof
  apply StatMech.FrontierA.ons_eastPortEdge_ne_northPortEdge L p q

/--
[triangularTorusDirectionStep_injective_public](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean)
-/
@[path]
private lemma triangularTorusDirectionStep_injective_public_eq
  {L : Nat}
  [Fact (2 < L)] :
-- imply
  Function.Injective (triangularTorusDirectionStep L) := by
-- proof
  apply StatMech.FrontierA.triangularTorusDirectionStep_injective_public L

/--
[triangularTorus_neighborFinset_steps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean)
-/
@[path]
private lemma triangularTorus_neighborFinset_steps_eq
  {L : Nat}
  [Fact (2 < L)]
  {p : ZMod L × ZMod L} :
-- imply
  (triangularTorusGraph L).neighborFinset p = Finset.univ.image (fun a : Fin 6 => p - triangularTorusDirectionStep L a) := by
-- proof
  apply StatMech.FrontierA.triangularTorus_neighborFinset_steps L p

/--
[triangularTorus_edgeBits_divergence_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean)
-/
@[path]
private lemma triangularTorus_edgeBits_divergence_zero_eq
  {L : Nat}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {p : ZMod L × ZMod L}
-- given
  (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L)) :
-- imply
  (ons_edgeBit F (triangularTorusEastEdge L p) : ZMod 2) + ons_edgeBit F (triangularTorusEastEdge L (p.1 - 1, p.2)) + ons_edgeBit F (triangularTorusNorthEdge L p) + ons_edgeBit F (triangularTorusNorthEdge L (p.1, p.2 - 1)) + ons_edgeBit F (triangularTorusNortheastEdge L p) + ons_edgeBit F (triangularTorusNortheastEdge L (p.1 - 1, p.2 - 1)) = 0 := by
-- proof
  apply StatMech.FrontierA.triangularTorus_edgeBits_divergence_zero L F hF p

/--
[triangularSquareExpansion_horizontalBit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean)
-/
@[path]
private lemma triangularSquareExpansion_horizontalBit_eq
  {L : Nat}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {p : ZMod L × ZMod L} :
-- imply
  ons_horizontalZBit (triangularSquareExpansion L F) p = (ons_edgeBit F (triangularTorusEastEdge L p) : ZMod 2) + (ons_edgeBit F (triangularTorusNortheastEdge L p) : ZMod 2) := by
-- proof
  apply StatMech.FrontierA.triangularSquareExpansion_horizontalBit L F p

/--
[triangularSquareExpansion_verticalBit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean)
-/
@[path]
private lemma triangularSquareExpansion_verticalBit_eq
  {L : Nat}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {p : ZMod L × ZMod L} :
-- imply
  ons_verticalZBit (triangularSquareExpansion L F) p = (ons_edgeBit F (triangularTorusNorthEdge L p) : ZMod 2) + (ons_edgeBit F (triangularTorusNortheastEdge L (p.1 - 1, p.2)) : ZMod 2) := by
-- proof
  apply StatMech.FrontierA.triangularSquareExpansion_verticalBit L F p

/--
[triangularSquareExpansion_subset_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean)
-/
@[path]
private lemma triangularSquareExpansion_subset_edgeFinset_eq
  {L : Nat}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))} :
-- imply
  triangularSquareExpansion L F ⊆ (onsTorusGraph L).edgeFinset := by
-- proof
  apply StatMech.FrontierA.triangularSquareExpansion_subset_edgeFinset L F

/--
[triangularSquareExpansion_evenSubgraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean)
-/
@[path]
private lemma triangularSquareExpansion_evenSubgraph_eq
  {L : Nat}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
-- given
  (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L)) :
-- imply
  triangularSquareExpansion L F ∈ StatMech.Ising.evenSubgraphs (onsTorusGraph L) := by
-- proof
  apply StatMech.FrontierA.triangularSquareExpansion_evenSubgraph L F hF

/--
[triangularPositiveEdgeReconstruction_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean)
-/
@[path]
private lemma triangularPositiveEdgeReconstruction_eq_eq
  {L : Nat}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
-- given
  (hF : F ⊆ (triangularTorusGraph L).edgeFinset) :
-- imply
  triangularPositiveEdgeReconstruction L F = F := by
-- proof
  apply StatMech.FrontierA.triangularPositiveEdgeReconstruction_eq L F hF

/--
[triangularPositiveEdgeReconstruction_pairwiseDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean)
-/
@[path]
private lemma triangularPositiveEdgeReconstruction_pairwiseDisjoint_eq
  {L : Nat}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))} :
-- imply
  ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint (fun a => (triangularPositiveEdgeSources L F a).image (triangularPositiveEdge L a)) := by
-- proof
  apply StatMech.FrontierA.triangularPositiveEdgeReconstruction_pairwiseDisjoint L F

/--
[sum_triangularPositiveEdgeSources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean)
-/
@[path]
private lemma sum_triangularPositiveEdgeSources_eq
  [AddCommMonoid A]
  {L : Nat}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {f : Sym2 (ZMod L × ZMod L) → A}
-- given
  (hF : F ⊆ (triangularTorusGraph L).edgeFinset) :
-- imply
  (∑ edge ∈ F, f edge) = ∑ a : Fin 3, ∑ p ∈ triangularPositiveEdgeSources L F a, f (triangularPositiveEdge L a p) := by
-- proof
  apply StatMech.FrontierA.sum_triangularPositiveEdgeSources L F hF f

/--
[triangularTorusXSeamEdge_positiveEdge_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean)
-/
@[path]
private lemma triangularTorusXSeamEdge_positiveEdge_iff_eq
  {L : Nat}
  [Fact (2 < L)]
  {a : Fin 3}
  {p : ZMod L × ZMod L} :
-- imply
  triangularTorusXSeamEdge L (triangularPositiveEdge L a p) ↔ (a = 0 ∨ a = 2) ∧ p.1 = -1 := by
-- proof
  apply StatMech.FrontierA.triangularTorusXSeamEdge_positiveEdge_iff L a p

/--
[triangularTorusYSeamEdge_positiveEdge_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean)
-/
@[path]
private lemma triangularTorusYSeamEdge_positiveEdge_iff_eq
  {L : Nat}
  [Fact (2 < L)]
  {a : Fin 3}
  {p : ZMod L × ZMod L} :
-- imply
  triangularTorusYSeamEdge L (triangularPositiveEdge L a p) ↔ (a = 1 ∨ a = 2) ∧ p.2 = -1 := by
-- proof
  apply StatMech.FrontierA.triangularTorusYSeamEdge_positiveEdge_iff L a p

/--
[triangularPositiveEdge_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean)
-/
@[path]
private lemma triangularPositiveEdge_zero_eq
  {L : Nat}
  [Fact (2 < L)]
  {p : ZMod L × ZMod L} :
-- imply
  triangularPositiveEdge L 0 p = triangularTorusEastEdge L p := by
-- proof
  apply StatMech.FrontierA.triangularPositiveEdge_zero L p

/--
[triangularPositiveEdge_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean)
-/
@[path]
private lemma triangularPositiveEdge_one_eq
  {L : Nat}
  [Fact (2 < L)]
  {p : ZMod L × ZMod L} :
-- imply
  triangularPositiveEdge L 1 p = triangularTorusNorthEdge L p := by
-- proof
  apply StatMech.FrontierA.triangularPositiveEdge_one L p

/--
[triangularPositiveEdge_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean)
-/
@[path]
private lemma triangularPositiveEdge_two_eq
  {L : Nat}
  [Fact (2 < L)]
  {p : ZMod L × ZMod L} :
-- imply
  triangularPositiveEdge L 2 p = triangularTorusNortheastEdge L p := by
-- proof
  apply StatMech.FrontierA.triangularPositiveEdge_two L p

/--
[triangularSquareExpansion_evenHomology](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean)
-/
@[path]
private lemma triangularSquareExpansion_evenHomology_eq
  {L : Nat}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
-- given
  (hF : F ⊆ (triangularTorusGraph L).edgeFinset) :
-- imply
  ons_evenHomology L (triangularSquareExpansion L F) = triangularTorusEvenHomology L F := by
-- proof
  apply StatMech.FrontierA.triangularSquareExpansion_evenHomology L F hF

/--
[zmodFinEquiv_two_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean)
-/
@[path]
private lemma zmodFinEquiv_two_apply_eq
  {a : Fin 2} :
-- imply
  (ZMod.finEquiv 2) a = (a : ZMod 2) := by
-- proof
  apply StatMech.FrontierA.zmodFinEquiv_two_apply a

/--
[triangularZeroHomology_eastCoeff_cast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean)
-/
@[path]
private lemma triangularZeroHomology_eastCoeff_cast_eq
  {L : Nat}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {p : ZMod L × ZMod L}
-- given
  (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L))
  (hhom : triangularTorusEvenHomology L F = 0) :
-- imply
  (triangularFaceEastCoeff (triangularZeroHomologyLowerPotential L F) (triangularZeroHomologyUpperPotential L F) p : ZMod 2) = ons_edgeBit F (triangularTorusEastEdge L p) := by
-- proof
  apply StatMech.FrontierA.triangularZeroHomology_eastCoeff_cast L F hF hhom p

/--
[triangularZeroHomology_northCoeff_cast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean)
-/
@[path]
private lemma triangularZeroHomology_northCoeff_cast_eq
  {L : Nat}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {p : ZMod L × ZMod L}
-- given
  (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L))
  (hhom : triangularTorusEvenHomology L F = 0) :
-- imply
  (triangularFaceNorthCoeff (triangularZeroHomologyLowerPotential L F) (triangularZeroHomologyUpperPotential L F) p : ZMod 2) = ons_edgeBit F (triangularTorusNorthEdge L p) := by
-- proof
  apply StatMech.FrontierA.triangularZeroHomology_northCoeff_cast L F hF hhom p

/--
[triangularZeroHomology_diagonalCoeff_cast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean)
-/
@[path]
private lemma triangularZeroHomology_diagonalCoeff_cast_eq
  {L : Nat}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {p : ZMod L × ZMod L} :
-- imply
  (triangularFaceDiagonalCoeff (triangularZeroHomologyLowerPotential L F) (triangularZeroHomologyUpperPotential L F) p : ZMod 2) = ons_edgeBit F (triangularTorusNortheastEdge L p) := by
-- proof
  apply StatMech.FrontierA.triangularZeroHomology_diagonalCoeff_cast L F p

/--
[triangularZeroHomology_eastCoeff_eq_zero_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean)
-/
@[path]
private lemma triangularZeroHomology_eastCoeff_eq_zero_of_not_mem_eq
  {L : Nat}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {p : ZMod L × ZMod L}
-- given
  (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L))
  (hhom : triangularTorusEvenHomology L F = 0)
  (hnot : triangularTorusEastEdge L p ∉ F) :
-- imply
  triangularFaceEastCoeff (triangularZeroHomologyLowerPotential L F) (triangularZeroHomologyUpperPotential L F) p = 0 := by
-- proof
  apply StatMech.FrontierA.triangularZeroHomology_eastCoeff_eq_zero_of_not_mem L F hF hhom p hnot

/--
[triangularZeroHomology_northCoeff_eq_zero_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean)
-/
@[path]
private lemma triangularZeroHomology_northCoeff_eq_zero_of_not_mem_eq
  {L : Nat}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {p : ZMod L × ZMod L}
-- given
  (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L))
  (hhom : triangularTorusEvenHomology L F = 0)
  (hnot : triangularTorusNorthEdge L p ∉ F) :
-- imply
  triangularFaceNorthCoeff (triangularZeroHomologyLowerPotential L F) (triangularZeroHomologyUpperPotential L F) p = 0 := by
-- proof
  apply StatMech.FrontierA.triangularZeroHomology_northCoeff_eq_zero_of_not_mem L F hF hhom p hnot

/--
[triangularZeroHomology_diagonalCoeff_eq_zero_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean)
-/
@[path]
private lemma triangularZeroHomology_diagonalCoeff_eq_zero_of_not_mem_eq
  {L : Nat}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {p : ZMod L × ZMod L}
-- given
  (hnot : triangularTorusNortheastEdge L p ∉ F) :
-- imply
  triangularFaceDiagonalCoeff (triangularZeroHomologyLowerPotential L F) (triangularZeroHomologyUpperPotential L F) p = 0 := by
-- proof
  apply StatMech.FrontierA.triangularZeroHomology_diagonalCoeff_eq_zero_of_not_mem L F p hnot

/--
[triangularZeroHomology_eastCoeff_ne_zero_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean)
-/
@[path]
private lemma triangularZeroHomology_eastCoeff_ne_zero_of_mem_eq
  {L : Nat}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {p : ZMod L × ZMod L}
-- given
  (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L))
  (hhom : triangularTorusEvenHomology L F = 0)
  (hmem : triangularTorusEastEdge L p ∈ F) :
-- imply
  triangularFaceEastCoeff (triangularZeroHomologyLowerPotential L F) (triangularZeroHomologyUpperPotential L F) p ≠ 0 := by
-- proof
  apply StatMech.FrontierA.triangularZeroHomology_eastCoeff_ne_zero_of_mem L F hF hhom p hmem

/--
[triangularZeroHomology_northCoeff_ne_zero_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean)
-/
@[path]
private lemma triangularZeroHomology_northCoeff_ne_zero_of_mem_eq
  {L : Nat}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {p : ZMod L × ZMod L}
-- given
  (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L))
  (hhom : triangularTorusEvenHomology L F = 0)
  (hmem : triangularTorusNorthEdge L p ∈ F) :
-- imply
  triangularFaceNorthCoeff (triangularZeroHomologyLowerPotential L F) (triangularZeroHomologyUpperPotential L F) p ≠ 0 := by
-- proof
  apply StatMech.FrontierA.triangularZeroHomology_northCoeff_ne_zero_of_mem L F hF hhom p hmem

/--
[triangularZeroHomology_diagonalCoeff_ne_zero_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean)
-/
@[path]
private lemma triangularZeroHomology_diagonalCoeff_ne_zero_of_mem_eq
  {L : Nat}
  [Fact (2 < L)]
  {F : Finset (Sym2 (ZMod L × ZMod L))}
  {p : ZMod L × ZMod L}
-- given
  (hmem : triangularTorusNortheastEdge L p ∈ F) :
-- imply
  triangularFaceDiagonalCoeff (triangularZeroHomologyLowerPotential L F) (triangularZeroHomologyUpperPotential L F) p ≠ 0 := by
-- proof
  apply StatMech.FrontierA.triangularZeroHomology_diagonalCoeff_ne_zero_of_mem L F p hmem


-- created on 2026-10-23
