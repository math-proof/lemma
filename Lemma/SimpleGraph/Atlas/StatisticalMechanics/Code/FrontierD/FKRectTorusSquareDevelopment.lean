import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment
open StatMech StatMech.FrontierD


/--
[fkRectSquareDevelopPoint_fst_sub_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma fkRectSquareDevelopPoint_fst_sub_snd_eq
  {p : Int × Int} :
-- imply
  (fkRectSquareDevelopPoint p).1 - (fkRectSquareDevelopPoint p).2 = p.2 := by
-- proof
  apply StatMech.FrontierD.fkRectSquareDevelopPoint_fst_sub_snd p

/--
[fkRectSquareDevelopPoint_snd_add_rowHalf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma fkRectSquareDevelopPoint_snd_add_rowHalf_eq
  {p : Int × Int} :
-- imply
  (fkRectSquareDevelopPoint p).2 + p.2 / 2 = p.1 := by
-- proof
  apply StatMech.FrontierD.fkRectSquareDevelopPoint_snd_add_rowHalf p

/--
[fkRectSquareDevelopPoint_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma fkRectSquareDevelopPoint_injective_eq :
-- imply
  Function.Injective fkRectSquareDevelopPoint := by
-- proof
  apply StatMech.FrontierD.fkRectSquareDevelopPoint_injective

/--
[fkRectSquareUndevelopPoint_developPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma fkRectSquareUndevelopPoint_developPoint_eq
  {p : Int × Int} :
-- imply
  fkRectSquareUndevelopPoint (fkRectSquareDevelopPoint p) = p := by
-- proof
  apply StatMech.FrontierD.fkRectSquareUndevelopPoint_developPoint p

/--
[fkRectSquareDevelopPoint_undevelopPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma fkRectSquareDevelopPoint_undevelopPoint_eq
  {p : Int × Int} :
-- imply
  fkRectSquareDevelopPoint (fkRectSquareUndevelopPoint p) = p := by
-- proof
  apply StatMech.FrontierD.fkRectSquareDevelopPoint_undevelopPoint p

/--
[fkRectSquareDevelopPoint_even_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma fkRectSquareDevelopPoint_even_vertical_eq
  {X k : Int} :
-- imply
  fkRectSquareDevelopPoint (X, 2 * k - 1) - fkRectSquareDevelopPoint (X, 2 * k) = (0, 1) := by
-- proof
  apply StatMech.FrontierD.fkRectSquareDevelopPoint_even_vertical X k

/--
[fkRectSquareDevelopPoint_even_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma fkRectSquareDevelopPoint_even_diagonal_eq
  {X k : Int} :
-- imply
  fkRectSquareDevelopPoint (X - 1, 2 * k - 1) - fkRectSquareDevelopPoint (X, 2 * k) = (-1, 0) := by
-- proof
  apply StatMech.FrontierD.fkRectSquareDevelopPoint_even_diagonal X k

/--
[fkRectSquareDevelopPoint_odd_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma fkRectSquareDevelopPoint_odd_vertical_eq
  {X k : Int} :
-- imply
  fkRectSquareDevelopPoint (X, 2 * k) - fkRectSquareDevelopPoint (X, 2 * k + 1) = (-1, 0) := by
-- proof
  apply StatMech.FrontierD.fkRectSquareDevelopPoint_odd_vertical X k

/--
[fkRectSquareDevelopPoint_odd_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma fkRectSquareDevelopPoint_odd_diagonal_eq
  {X k : Int} :
-- imply
  fkRectSquareDevelopPoint (X, 2 * k) - fkRectSquareDevelopPoint (X - 1, 2 * k + 1) = (0, 1) := by
-- proof
  apply StatMech.FrontierD.fkRectSquareDevelopPoint_odd_diagonal X k

/--
[fkRectLiftedIndexedEdgeEnds_squareStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma fkRectLiftedIndexedEdgeEnds_squareStep_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex} :
-- imply
  fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).2 - fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).1 = (-1, 0) ∨ fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).2 - fkRectSquareDevelopPoint (fkRectLiftedIndexedEdgeEnds R e).1 = (0, 1) := by
-- proof
  apply StatMech.FrontierD.fkRectLiftedIndexedEdgeEnds_squareStep R e

/--
[fkRectSquareDeckHom_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma fkRectSquareDeckHom_injective_eq
  {R : FKRectTorus} :
-- imply
  Function.Injective (fkRectSquareDeckHom R) := by
-- proof
  apply StatMech.FrontierD.fkRectSquareDeckHom_injective R

/--
[mem_fkRectSquareDeckLattice_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma mem_fkRectSquareDeckLattice_iff_eq
  {R : FKRectTorus}
  {z : Int × Int} :
-- imply
  z ∈ fkRectSquareDeckLattice R ↔ ∃ u : Int × Int, fkRectSquareDeckTranslation R u = z := by
-- proof
  apply StatMech.FrontierD.mem_fkRectSquareDeckLattice_iff R z

/--
[fkRectSquareDevelopPoint_add_period](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma fkRectSquareDevelopPoint_add_period_eq
  {R : FKRectTorus}
  {p u : Int × Int} :
-- imply
  fkRectSquareDevelopPoint (p.1 + (R.width : Int) * u.1, p.2 + (R.height : Int) * u.2) - fkRectSquareDevelopPoint p = fkRectSquareDeckTranslation R u := by
-- proof
  apply StatMech.FrontierD.fkRectSquareDevelopPoint_add_period R p u

/--
[fkRectSquareUndevelopPoint_add_deck](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma fkRectSquareUndevelopPoint_add_deck_eq
  {R : FKRectTorus}
  {p u : Int × Int} :
-- imply
  fkRectSquareUndevelopPoint (p + fkRectSquareDeckTranslation R u) = ((fkRectSquareUndevelopPoint p).1 + (R.width : Int) * u.1, (fkRectSquareUndevelopPoint p).2 + (R.height : Int) * u.2) := by
-- proof
  apply StatMech.FrontierD.fkRectSquareUndevelopPoint_add_deck R p u

/--
[fkRectVertexSquareClass_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma fkRectVertexSquareClass_injective_eq
  {R : FKRectTorus} :
-- imply
  Function.Injective (fkRectVertexSquareClass R) := by
-- proof
  apply StatMech.FrontierD.fkRectVertexSquareClass_injective R

/--
[fkRectIntModFin_natCast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma fkRectIntModFin_natCast_eq
  {N : Nat}
  {i : Fin N}
-- given
  (hN : 0 < N) :
-- imply
  fkRectIntModFin hN (i.val : Int) = i := by
-- proof
  apply StatMech.FrontierD.fkRectIntModFin_natCast hN i

/--
[fkRectIntModFin_natCast_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma fkRectIntModFin_natCast_sub_one_eq
  {N : Nat}
  {i : Fin N}
-- given
  (hN : 0 < N) :
-- imply
  fkRectIntModFin hN ((i.val : Int) - 1) = SixVertexArrows.cyclicPred hN i := by
-- proof
  apply StatMech.FrontierD.fkRectIntModFin_natCast_sub_one hN i

/--
[fkRectSquareRepresentativeVertex_developPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma fkRectSquareRepresentativeVertex_developPoint_eq
  {R : FKRectTorus}
  {p : Int × Int} :
-- imply
  fkRectSquareRepresentativeVertex R (fkRectSquareDevelopPoint p) = fkRectLiftedVertex R p := by
-- proof
  apply StatMech.FrontierD.fkRectSquareRepresentativeVertex_developPoint R p

/--
[fkRectVertexSquareClass_representative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma fkRectVertexSquareClass_representative_eq
  {R : FKRectTorus}
  {z : Int × Int} :
-- imply
  fkRectVertexSquareClass R (fkRectSquareRepresentativeVertex R z) = QuotientAddGroup.mk z := by
-- proof
  apply StatMech.FrontierD.fkRectVertexSquareClass_representative R z

/--
[fkRectVertexSquareClass_liftedVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma fkRectVertexSquareClass_liftedVertex_eq
  {R : FKRectTorus}
  {p : Int × Int} :
-- imply
  fkRectVertexSquareClass R (fkRectLiftedVertex R p) = QuotientAddGroup.mk (fkRectSquareDevelopPoint p) := by
-- proof
  apply StatMech.FrontierD.fkRectVertexSquareClass_liftedVertex R p

/--
[fkRectLiftedIndexedEdgeEnds_project](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma fkRectLiftedIndexedEdgeEnds_project_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex} :
-- imply
  fkRectTorusIndexedEdge R e = s(fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R e).1, fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R e).2) := by
-- proof
  apply StatMech.FrontierD.fkRectLiftedIndexedEdgeEnds_project R e

/--
[fkRectLiftedIndexedEdgeEnds_developedStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma fkRectLiftedIndexedEdgeEnds_developedStep_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex} :
-- imply
  fkRectDevelopedStep R (fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R e).1) (fkRectLiftedVertex R (fkRectLiftedIndexedEdgeEnds R e).2) = (fkRectLiftedIndexedEdgeEnds R e).2 - (fkRectLiftedIndexedEdgeEnds R e).1 := by
-- proof
  apply StatMech.FrontierD.fkRectLiftedIndexedEdgeEnds_developedStep R e

/--
[fkRectIndexedEdge_squareLift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma fkRectIndexedEdge_squareLift_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex} :
-- imply
  ∃ p q : Int × Int, fkRectTorusIndexedEdge R e = s(fkRectLiftedVertex R p, fkRectLiftedVertex R q) ∧ fkRectVertexSquareClass R (fkRectLiftedVertex R p) = QuotientAddGroup.mk (fkRectSquareDevelopPoint p) ∧ fkRectVertexSquareClass R (fkRectLiftedVertex R q) = QuotientAddGroup.mk (fkRectSquareDevelopPoint q) ∧ fkRectDevelopedStep R (fkRectLiftedVertex R p) (fkRectLiftedVertex R q) = q - p ∧ (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p = (-1, 0) ∨ fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p = (0, 1)) := by
-- proof
  apply StatMech.FrontierD.fkRectIndexedEdge_squareLift R e

/--
[fkRectLiftedVertex_eq_iff_exists_period](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma fkRectLiftedVertex_eq_iff_exists_period_eq
  {R : FKRectTorus}
  {p q : Int × Int} :
-- imply
  fkRectLiftedVertex R p = fkRectLiftedVertex R q ↔ ∃ u : Int × Int, p = (q.1 + (R.width : Int) * u.1, q.2 + (R.height : Int) * u.2) := by
-- proof
  apply StatMech.FrontierD.fkRectLiftedVertex_eq_iff_exists_period R p q

/--
[FKRectSquareAxisStep.symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma symm_eq
  {p q : Int × Int}
-- given
  (h : FKRectSquareAxisStep p q) :
-- imply
  FKRectSquareAxisStep q p := by
-- proof
  apply StatMech.FrontierD.FKRectSquareAxisStep.symm h

/--
[fkRectSquareDevelopPoint_sub_add_period](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma fkRectSquareDevelopPoint_sub_add_period_eq
  {R : FKRectTorus}
  {p q u : Int × Int} :
-- imply
  fkRectSquareDevelopPoint (q.1 + (R.width : Int) * u.1, q.2 + (R.height : Int) * u.2) - fkRectSquareDevelopPoint (p.1 + (R.width : Int) * u.1, p.2 + (R.height : Int) * u.2) = fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p := by
-- proof
  apply StatMech.FrontierD.fkRectSquareDevelopPoint_sub_add_period R p q u

/--
[fkRectTorusGraph_adj_squareLift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma fkRectTorusGraph_adj_squareLift_eq
  {R : FKRectTorus}
  {x y : R.Vertex}
  {p : Int × Int}
-- given
  (hxy : (fkRectTorusGraph R).Adj x y)
  (hp : fkRectLiftedVertex R p = x) :
-- imply
  ∃ q : Int × Int, fkRectLiftedVertex R q = y ∧ q - p = fkRectDevelopedStep R x y ∧ FKRectSquareAxisStep (fkRectSquareDevelopPoint p) (fkRectSquareDevelopPoint q) := by
-- proof
  apply StatMech.FrontierD.fkRectTorusGraph_adj_squareLift R hxy p hp

/--
[fkRectWalk_exists_squareLift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma fkRectWalk_exists_squareLift_eq
  {R : FKRectTorus}
  {G : SimpleGraph R.Vertex}
  {x y : R.Vertex}
  {w : G.Walk x y}
  {p : Int × Int}
-- given
  (hsub : G ≤ fkRectTorusGraph R)
  (hp : fkRectLiftedVertex R p = x) :
-- imply
  ∃ q : Int × Int, FKRectSquareWalkLift R w p q := by
-- proof
  apply StatMech.FrontierD.fkRectWalk_exists_squareLift R hsub w p hp

/--
[FKRectSquareWalkLift.end_project](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma end_project_eq
  {R : FKRectTorus}
  {G : SimpleGraph R.Vertex}
  {x y : R.Vertex}
  {w : G.Walk x y}
  {p q : Int × Int}
-- given
  (h : FKRectSquareWalkLift R w p q) :
-- imply
  fkRectLiftedVertex R q = y := by
-- proof
  apply StatMech.FrontierD.FKRectSquareWalkLift.end_project R h

/--
[FKRectSquareWalkLift.sub_eq_developedDisplacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma sub_eq_developedDisplacement_eq
  {R : FKRectTorus}
  {G : SimpleGraph R.Vertex}
  {x y : R.Vertex}
  {w : G.Walk x y}
  {p q : Int × Int}
-- given
  (h : FKRectSquareWalkLift R w p q) :
-- imply
  q - p = fkRectWalkDevelopedDisplacement R w := by
-- proof
  apply StatMech.FrontierD.FKRectSquareWalkLift.sub_eq_developedDisplacement R h

/--
[FKRectSquareWalkLift.closed_end_eq_period_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma closed_end_eq_period_winding_eq
  {R : FKRectTorus}
  {G : SimpleGraph R.Vertex}
  {x : R.Vertex}
  {w : G.Walk x x}
  {p q : Int × Int}
-- given
  (h : FKRectSquareWalkLift R w p q) :
-- imply
  q = (p.1 + (R.width : Int) * (fkRectWalkWinding R w).1, p.2 + (R.height : Int) * (fkRectWalkWinding R w).2) := by
-- proof
  apply StatMech.FrontierD.FKRectSquareWalkLift.closed_end_eq_period_winding R h

/--
[FKRectSquareWalkLift.closed_develop_sub_eq_deck_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma closed_develop_sub_eq_deck_winding_eq
  {R : FKRectTorus}
  {G : SimpleGraph R.Vertex}
  {x : R.Vertex}
  {w : G.Walk x x}
  {p q : Int × Int}
-- given
  (h : FKRectSquareWalkLift R w p q) :
-- imply
  fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p = fkRectSquareDeckTranslation R (fkRectWalkWinding R w) := by
-- proof
  apply StatMech.FrontierD.FKRectSquareWalkLift.closed_develop_sub_eq_deck_winding R h

/--
[fkRectVertexSquareClass_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma fkRectVertexSquareClass_surjective_eq
  {R : FKRectTorus} :
-- imply
  Function.Surjective (fkRectVertexSquareClass R) := by
-- proof
  apply StatMech.FrontierD.fkRectVertexSquareClass_surjective R

/--
[fkRectSquareDeckTranslation_det](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma fkRectSquareDeckTranslation_det_eq
  {R : FKRectTorus}
  {u v : Int × Int} :
-- imply
  (fkRectSquareDeckTranslation R u).1 * (fkRectSquareDeckTranslation R v).2 - (fkRectSquareDeckTranslation R u).2 * (fkRectSquareDeckTranslation R v).1 = -(R.width : Int) * R.height * (u.1 * v.2 - u.2 * v.1) := by
-- proof
  apply StatMech.FrontierD.fkRectSquareDeckTranslation_det R u v

/--
[fkRectWindingIndependent_squareDeck_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma fkRectWindingIndependent_squareDeck_iff_eq
  {R : FKRectTorus}
  {u v : Int × Int} :
-- imply
  FKRectWindingIndependent (fkRectSquareDeckTranslation R u) (fkRectSquareDeckTranslation R v) ↔ FKRectWindingIndependent u v := by
-- proof
  apply StatMech.FrontierD.fkRectWindingIndependent_squareDeck_iff R u v

/--
[FKRectSquareWalkLift.closed_developedIndependent_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma closed_developedIndependent_iff_eq
  {R : FKRectTorus}
  {G H : SimpleGraph R.Vertex}
  {x y : R.Vertex}
  {w : G.Walk x x}
  {z : H.Walk y y}
  {p q a b : Int × Int}
-- given
  (hw : FKRectSquareWalkLift R w p q)
  (hz : FKRectSquareWalkLift R z a b) :
-- imply
  FKRectWindingIndependent (fkRectSquareDevelopPoint q - fkRectSquareDevelopPoint p) (fkRectSquareDevelopPoint b - fkRectSquareDevelopPoint a) ↔ FKRectWindingIndependent (fkRectWalkWinding R w) (fkRectWalkWinding R z) := by
-- proof
  apply StatMech.FrontierD.FKRectSquareWalkLift.closed_developedIndependent_iff R hw hz

/--
[fkRectOpenGraph_le_torusGraph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma fkRectOpenGraph_le_torusGraph_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectOpenGraph R omega ≤ fkRectTorusGraph R := by
-- proof
  apply StatMech.FrontierD.fkRectOpenGraph_le_torusGraph R omega

/--
[fkRectHasSquareLiftNet_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSquareDevelopment.lean)
-/
@[path]
private lemma fkRectHasSquareLiftNet_iff_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  FKRectHasSquareLiftNet R omega ↔ FKRectHasNet R omega := by
-- proof
  apply StatMech.FrontierD.fkRectHasSquareLiftNet_iff R omega


-- created on 2026-10-23
