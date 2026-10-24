import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectFaithfulShearCoordinates
open StatMech StatMech.FrontierD


/--
[fkRectRowParityTerm_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulShearCoordinates.lean)
-/
@[path]
private lemma fkRectRowParityTerm_bounds_eq
  {y : Int} :
-- imply
  0 ≤ (y + 1) / 2 - y / 2 ∧ (y + 1) / 2 - y / 2 ≤ 1 := by
-- proof
  apply StatMech.FrontierD.fkRectRowParityTerm_bounds y

/--
[fkRectFaithfulShearPoint_apply_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulShearCoordinates.lean)
-/
@[path]
private lemma fkRectFaithfulShearPoint_apply_zero_eq
  {p : Int × Int} :
-- imply
  (fkRectFaithfulShearPoint p) 0 = 2 * (p.1 + p.2) := by
-- proof
  apply StatMech.FrontierD.fkRectFaithfulShearPoint_apply_zero p

/--
[fkRectFaithfulShearPoint_apply_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulShearCoordinates.lean)
-/
@[path]
private lemma fkRectFaithfulShearPoint_apply_one_eq
  {p : Int × Int} :
-- imply
  (fkRectFaithfulShearPoint p) 1 = 2 * (p.1 - p.2) := by
-- proof
  apply StatMech.FrontierD.fkRectFaithfulShearPoint_apply_one p

/--
[fkRectFaithfulShearPoint_refinedScale_develop_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulShearCoordinates.lean)
-/
@[path]
private lemma fkRectFaithfulShearPoint_refinedScale_develop_fst_eq
  {p : Int × Int} :
-- imply
  (fkRectFaithfulShearPoint (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p))) 0 = 16 * p.1 + 8 * ((p.2 + 1) / 2 - p.2 / 2) := by
-- proof
  apply StatMech.FrontierD.fkRectFaithfulShearPoint_refinedScale_develop_fst p

/--
[fkRectFaithfulShearPoint_refinedScale_develop_snd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulShearCoordinates.lean)
-/
@[path]
private lemma fkRectFaithfulShearPoint_refinedScale_develop_snd_eq
  {p : Int × Int} :
-- imply
  (fkRectFaithfulShearPoint (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p))) 1 = 8 * p.2 := by
-- proof
  apply StatMech.FrontierD.fkRectFaithfulShearPoint_refinedScale_develop_snd p

/--
[fkRectFaithfulShearPoint_refinedDualScale_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulShearCoordinates.lean)
-/
@[path]
private lemma fkRectFaithfulShearPoint_refinedDualScale_eq_eq
  {p : Int × Int} :
-- imply
  fkRectFaithfulShearPoint (fkRectRefinedDualScalePoint p) = ![(fkRectFaithfulShearPoint (fkRectRefinedScalePoint p)) 0 + 8, (fkRectFaithfulShearPoint (fkRectRefinedScalePoint p)) 1] := by
-- proof
  apply StatMech.FrontierD.fkRectFaithfulShearPoint_refinedDualScale_eq p

/--
[fkRectFaithfulShearPoint_refinedScale_develop_fst_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulShearCoordinates.lean)
-/
@[path]
private lemma fkRectFaithfulShearPoint_refinedScale_develop_fst_bounds_eq
  {p : Int × Int}
  {left right : Int}
-- given
  (hleft : left ≤ p.1)
  (hright : p.1 ≤ right) :
-- imply
  16 * left ≤ (fkRectFaithfulShearPoint (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p))) 0 ∧ (fkRectFaithfulShearPoint (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p))) 0 ≤ 16 * right + 8 := by
-- proof
  apply StatMech.FrontierD.fkRectFaithfulShearPoint_refinedScale_develop_fst_bounds p left right hleft hright

/--
[fkRectFaithfulShearDartRoute_fst_between](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulShearCoordinates.lean)
-/
@[path]
private lemma fkRectFaithfulShearDartRoute_fst_between_eq
  {d : FKRectIntegralSquareDart}
  {r : Int × Int}
-- given
  (hr : r ∈ fkRectFaithfulShearDartRoute d) :
-- imply
  min (fkRectFaithfulShearPair d.1).1 (fkRectFaithfulShearPair (fkRectIntegralSquareDartEnd d)).1 ≤ r.1 ∧ r.1 ≤ max (fkRectFaithfulShearPair d.1).1 (fkRectFaithfulShearPair (fkRectIntegralSquareDartEnd d)).1 := by
-- proof
  apply StatMech.FrontierD.fkRectFaithfulShearDartRoute_fst_between d r hr

/--
[fkRectFaithfulShearDartRoute_reverse_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulShearCoordinates.lean)
-/
@[path]
private lemma fkRectFaithfulShearDartRoute_reverse_iff_eq
  {d : FKRectIntegralSquareDart}
  {r : Int × Int} :
-- imply
  r ∈ fkRectFaithfulShearDartRoute (fkRectIntegralSquareDartReverse d) ↔ r ∈ fkRectFaithfulShearDartRoute d := by
-- proof
  apply StatMech.FrontierD.fkRectFaithfulShearDartRoute_reverse_iff d r

/--
[fkRectRefinedPrimalEdgeEnd_eq_start_axis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulShearCoordinates.lean)
-/
@[path]
private lemma fkRectRefinedPrimalEdgeEnd_eq_start_axis_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex} :
-- imply
  fkRectRefinedPrimalEdgeEnd R e = if fkRectClosedPairingAtEdge e then ((fkRectRefinedPrimalEdgeStart R e).1 - 4, (fkRectRefinedPrimalEdgeStart R e).2) else ((fkRectRefinedPrimalEdgeStart R e).1, (fkRectRefinedPrimalEdgeStart R e).2 + 4) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedPrimalEdgeEnd_eq_start_axis R e

/--
[fkRectRefinedPrimalEdgeBlock_faithfulRoute_fst_between](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulShearCoordinates.lean)
-/
@[path]
private lemma fkRectRefinedPrimalEdgeBlock_faithfulRoute_fst_between_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex}
  {t : Int × Int}
  {d : FKRectIntegralSquareDart}
  {r : Int × Int}
-- given
  (hd : d ∈ (fkRectRefinedPrimalEdgeDarts R e).map (fkRectIntegralSquareDartTranslate t))
  (hr : r ∈ fkRectFaithfulShearDartRoute d) :
-- imply
  min (fkRectFaithfulShearPair ((fkRectRefinedPrimalEdgeStart R e).1 + t.1, (fkRectRefinedPrimalEdgeStart R e).2 + t.2)).1 (fkRectFaithfulShearPair ((fkRectRefinedPrimalEdgeEnd R e).1 + t.1, (fkRectRefinedPrimalEdgeEnd R e).2 + t.2)).1 ≤ r.1 ∧ r.1 ≤ max (fkRectFaithfulShearPair ((fkRectRefinedPrimalEdgeStart R e).1 + t.1, (fkRectRefinedPrimalEdgeStart R e).2 + t.2)).1 (fkRectFaithfulShearPair ((fkRectRefinedPrimalEdgeEnd R e).1 + t.1, (fkRectRefinedPrimalEdgeEnd R e).2 + t.2)).1 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedPrimalEdgeBlock_faithfulRoute_fst_between R e t d r hd hr

/--
[fkRectRefinedPrimalEdgeReverseBlock_faithfulRoute_fst_between](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulShearCoordinates.lean)
-/
@[path]
private lemma fkRectRefinedPrimalEdgeReverseBlock_faithfulRoute_fst_between_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex}
  {t : Int × Int}
  {d : FKRectIntegralSquareDart}
  {r : Int × Int}
-- given
  (hd : d ∈ (fkRectIntegralSquareDartListReverse (fkRectRefinedPrimalEdgeDarts R e)).map (fkRectIntegralSquareDartTranslate t))
  (hr : r ∈ fkRectFaithfulShearDartRoute d) :
-- imply
  min (fkRectFaithfulShearPair ((fkRectRefinedPrimalEdgeStart R e).1 + t.1, (fkRectRefinedPrimalEdgeStart R e).2 + t.2)).1 (fkRectFaithfulShearPair ((fkRectRefinedPrimalEdgeEnd R e).1 + t.1, (fkRectRefinedPrimalEdgeEnd R e).2 + t.2)).1 ≤ r.1 ∧ r.1 ≤ max (fkRectFaithfulShearPair ((fkRectRefinedPrimalEdgeStart R e).1 + t.1, (fkRectRefinedPrimalEdgeStart R e).2 + t.2)).1 (fkRectFaithfulShearPair ((fkRectRefinedPrimalEdgeEnd R e).1 + t.1, (fkRectRefinedPrimalEdgeEnd R e).2 + t.2)).1 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedPrimalEdgeReverseBlock_faithfulRoute_fst_between R e t d r hd hr

/--
[fkRectRefinedDualEdgeEnd_eq_start_axis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulShearCoordinates.lean)
-/
@[path]
private lemma fkRectRefinedDualEdgeEnd_eq_start_axis_eq
  {R : FKRectTorus}
  {d : R.EdgeIndex} :
-- imply
  fkRectRefinedDualEdgeEnd R d = if fkRectClosedPairingAtEdge d then ((fkRectRefinedDualEdgeStart R d).1 - 4, (fkRectRefinedDualEdgeStart R d).2) else ((fkRectRefinedDualEdgeStart R d).1, (fkRectRefinedDualEdgeStart R d).2 + 4) := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedDualEdgeEnd_eq_start_axis R d

/--
[fkRectRefinedDualEdgeBlock_faithfulRoute_fst_between](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulShearCoordinates.lean)
-/
@[path]
private lemma fkRectRefinedDualEdgeBlock_faithfulRoute_fst_between_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex}
  {t : Int × Int}
  {d : FKRectIntegralSquareDart}
  {r : Int × Int}
-- given
  (hd : d ∈ (fkRectRefinedDualEdgeDarts R e).map (fkRectIntegralSquareDartTranslate t))
  (hr : r ∈ fkRectFaithfulShearDartRoute d) :
-- imply
  min (fkRectFaithfulShearPair ((fkRectRefinedDualEdgeStart R e).1 + t.1, (fkRectRefinedDualEdgeStart R e).2 + t.2)).1 (fkRectFaithfulShearPair ((fkRectRefinedDualEdgeEnd R e).1 + t.1, (fkRectRefinedDualEdgeEnd R e).2 + t.2)).1 ≤ r.1 ∧ r.1 ≤ max (fkRectFaithfulShearPair ((fkRectRefinedDualEdgeStart R e).1 + t.1, (fkRectRefinedDualEdgeStart R e).2 + t.2)).1 (fkRectFaithfulShearPair ((fkRectRefinedDualEdgeEnd R e).1 + t.1, (fkRectRefinedDualEdgeEnd R e).2 + t.2)).1 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedDualEdgeBlock_faithfulRoute_fst_between R e t d r hd hr

/--
[fkRectRefinedDualEdgeReverseBlock_faithfulRoute_fst_between](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulShearCoordinates.lean)
-/
@[path]
private lemma fkRectRefinedDualEdgeReverseBlock_faithfulRoute_fst_between_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex}
  {t : Int × Int}
  {d : FKRectIntegralSquareDart}
  {r : Int × Int}
-- given
  (hd : d ∈ (fkRectIntegralSquareDartListReverse (fkRectRefinedDualEdgeDarts R e)).map (fkRectIntegralSquareDartTranslate t))
  (hr : r ∈ fkRectFaithfulShearDartRoute d) :
-- imply
  min (fkRectFaithfulShearPair ((fkRectRefinedDualEdgeStart R e).1 + t.1, (fkRectRefinedDualEdgeStart R e).2 + t.2)).1 (fkRectFaithfulShearPair ((fkRectRefinedDualEdgeEnd R e).1 + t.1, (fkRectRefinedDualEdgeEnd R e).2 + t.2)).1 ≤ r.1 ∧ r.1 ≤ max (fkRectFaithfulShearPair ((fkRectRefinedDualEdgeStart R e).1 + t.1, (fkRectRefinedDualEdgeStart R e).2 + t.2)).1 (fkRectFaithfulShearPair ((fkRectRefinedDualEdgeEnd R e).1 + t.1, (fkRectRefinedDualEdgeEnd R e).2 + t.2)).1 := by
-- proof
  apply StatMech.FrontierD.fkRectRefinedDualEdgeReverseBlock_faithfulRoute_fst_between R e t d r hd hr

/--
[fkRectFaithfulShearPoint_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulShearCoordinates.lean)
-/
@[path]
private lemma fkRectFaithfulShearPoint_add_eq
  {p u : Int × Int} :
-- imply
  fkRectFaithfulShearPoint (p.1 + u.1, p.2 + u.2) = ![(fkRectFaithfulShearPoint p) 0 + 2 * (u.1 + u.2), (fkRectFaithfulShearPoint p) 1 + 2 * (u.1 - u.2)] := by
-- proof
  apply StatMech.FrontierD.fkRectFaithfulShearPoint_add p u

/--
[fkRectFaithfulShearPoint_add_refinedDeck](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulShearCoordinates.lean)
-/
@[path]
private lemma fkRectFaithfulShearPoint_add_refinedDeck_eq
  {R : FKRectTorus}
  {p u : Int × Int} :
-- imply
  fkRectFaithfulShearPoint (p.1 + (fkRectRefinedDeckTranslation R u).1, p.2 + (fkRectRefinedDeckTranslation R u).2) = ![(fkRectFaithfulShearPoint p) 0 + 16 * (R.width : Int) * u.1, (fkRectFaithfulShearPoint p) 1 + 8 * (R.height : Int) * u.2] := by
-- proof
  apply StatMech.FrontierD.fkRectFaithfulShearPoint_add_refinedDeck R p u

/--
[FKRectSquareWalkLift.closed_faithfulRefined_end_of_verticalOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulShearCoordinates.lean)
-/
@[path]
private lemma closed_faithfulRefined_end_of_verticalOne_eq
  {R : FKRectTorus}
  {G : SimpleGraph R.Vertex}
  {x : R.Vertex}
  {w : G.Walk x x}
  {p q : Int × Int}
-- given
  (h : FKRectSquareWalkLift R w p q)
  (hw : fkRectWalkWinding R w = (0, 1)) :
-- imply
  fkRectFaithfulShearPoint (fkRectRefinedScalePoint (fkRectSquareDevelopPoint q)) = ![(fkRectFaithfulShearPoint (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p))) 0, (fkRectFaithfulShearPoint (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p))) 1 + 8 * (R.height : Int)] := by
-- proof
  apply StatMech.FrontierD.FKRectSquareWalkLift.closed_faithfulRefined_end_of_verticalOne R h hw


-- created on 2026-10-23
