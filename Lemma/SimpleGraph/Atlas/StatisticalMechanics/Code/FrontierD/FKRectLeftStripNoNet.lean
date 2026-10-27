import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectLeftStripNoNet.Part2
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectTorusGraph_adj_crosses_column_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectLeftStripNoNet.lean)
-/
@[path]
private lemma fkRectTorusGraph_adj_crosses_column_cut_eq
  {R : FKRectTorus}
  {right : Nat}
  {u v : R.Vertex}
-- given
  (hright : right + 1 < R.width)
  (hu : u.1.val ≤ right)
  (hv : right < v.1.val)
  (hadj : (fkRectTorusGraph R).Adj u v)
  (hnot : ¬ fkRectCrossesHorizontalSeam R s(u, v)) :
-- imply
  u.1.val = right ∧ v.1.val = right + 1 := by
-- proof
  apply StatMech.FrontierD.fkRectTorusGraph_adj_crosses_column_cut R right hright hu hv hadj hnot

/--
[fkRectLeftStripRightPotential_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectLeftStripNoNet.lean)
-/
@[path]
private lemma fkRectLeftStripRightPotential_outside_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {right : Nat}
  {v : R.Vertex}
-- given
  (hv : v ∉ fkRectLeftStrip R right) :
-- imply
  fkRectLeftStripRightPotential R omega right v = 1 := by
-- proof
  apply StatMech.FrontierD.fkRectLeftStripRightPotential_outside R omega right v hv

/--
[fkRectLeftStripRightPotential_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectLeftStripNoNet.lean)
-/
@[path]
private lemma fkRectLeftStripRightPotential_right_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {right : Nat}
  {v : R.Vertex}
-- given
  (hv : v ∈ fkRectLeftStrip R right)
  (hcol : v.1.val = right) :
-- imply
  fkRectLeftStripRightPotential R omega right v = 1 := by
-- proof
  apply StatMech.FrontierD.fkRectLeftStripRightPotential_right R omega right hv hcol

/--
[fkRectLeftStripRightPotential_left_eq_zero_of_noCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectLeftStripNoNet.lean)
-/
@[path]
private lemma fkRectLeftStripRightPotential_left_eq_zero_of_noCrossing_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {right : Nat}
  {v : R.Vertex}
-- given
  (hno : omega ∈ fkRectNoLeftStripCrossingEvent R right)
  (hcol : v.1.val = 0) :
-- imply
  fkRectLeftStripRightPotential R omega right v = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectLeftStripRightPotential_left_eq_zero_of_noCrossing R omega right hno v hcol

/--
[fkRectLeftStripRightPotential_eq_of_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectLeftStripNoNet.lean)
-/
@[path]
private lemma fkRectLeftStripRightPotential_eq_of_connected_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {right : Nat}
  {u v : R.Vertex}
-- given
  (hu : u ∈ fkRectLeftStrip R right)
  (hv : v ∈ fkRectLeftStrip R right)
  (huv : FKRectConnectedWithin R omega (fkRectLeftStrip R right) ⟨u, hu⟩ ⟨v, hv⟩) :
-- imply
  fkRectLeftStripRightPotential R omega right u = fkRectLeftStripRightPotential R omega right v := by
-- proof
  apply StatMech.FrontierD.fkRectLeftStripRightPotential_eq_of_connected R omega right hu hv huv

/--
[fkRectHorizontalSeamIncrement_eq_zero_of_not_crosses_leftStrip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectLeftStripNoNet.lean)
-/
@[path]
private lemma fkRectHorizontalSeamIncrement_eq_zero_of_not_crosses_leftStrip_eq
  {R : FKRectTorus}
  {u v : R.Vertex}
-- given
  (hnot : ¬ fkRectCrossesHorizontalSeam R s(u, v)) :
-- imply
  fkRectHorizontalSeamIncrement R u v = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalSeamIncrement_eq_zero_of_not_crosses_leftStrip R u v hnot

/--
[fkRectHorizontalIncrement_eq_leftStripPotential_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectLeftStripNoNet.lean)
-/
@[path]
private lemma fkRectHorizontalIncrement_eq_leftStripPotential_sub_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {right : Nat}
  {u v : R.Vertex}
-- given
  (hright : right + 1 < R.width)
  (hno : omega ∈ fkRectNoLeftStripCrossingEvent R right)
  (huv : (fkRectOpenGraph R omega).Adj u v) :
-- imply
  fkRectHorizontalSeamIncrement R u v = fkRectLeftStripRightPotential R omega right u - fkRectLeftStripRightPotential R omega right v := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalIncrement_eq_leftStripPotential_sub R omega right hright hno huv

/--
[fkRectClosedWalk_winding_fst_eq_zero_of_noLeftStripCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectLeftStripNoNet.lean)
-/
@[path]
private lemma fkRectClosedWalk_winding_fst_eq_zero_of_noLeftStripCrossing_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {right : Nat}
  {x : R.Vertex}
  {p : (fkRectOpenGraph R omega).Walk x x}
-- given
  (hright : right + 1 < R.width)
  (hno : omega ∈ fkRectNoLeftStripCrossingEvent R right) :
-- imply
  (fkRectWalkWinding R p).1 = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectClosedWalk_winding_fst_eq_zero_of_noLeftStripCrossing R omega right hright hno p

/--
[not_fkRectHasNet_of_noLeftStripCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectLeftStripNoNet.lean)
-/
@[path]
private lemma not_fkRectHasNet_of_noLeftStripCrossing_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {right : Nat}
-- given
  (hright : right + 1 < R.width)
  (hno : omega ∈ fkRectNoLeftStripCrossingEvent R right) :
-- imply
  ¬ FKRectHasNet R omega := by
-- proof
  apply StatMech.FrontierD.not_fkRectHasNet_of_noLeftStripCrossing R omega right hright hno


-- created on 2026-10-23
