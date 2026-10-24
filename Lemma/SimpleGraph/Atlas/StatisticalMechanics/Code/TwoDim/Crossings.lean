import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.TwoDim.Crossings
open Set StatMech StatMech.TwoDim


/--
[mem_rectangle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/Crossings.lean)
-/
@[path]
private lemma mem_rectangle_eq
  {a b : ℤ}
  {x : Site 2} :
-- imply
  x ∈ rectangle a b ↔ 0 ≤ x 0 ∧ x 0 ≤ a ∧ 0 ≤ x 1 ∧ x 1 ≤ b := by
-- proof
  apply StatMech.TwoDim.mem_rectangle

/--
[rectangle_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/Crossings.lean)
-/
@[path]
private lemma rectangle_finite_eq
  {a b : ℤ}
  {a b : ℤ} :
-- imply
  (rectangle a b).Finite := by
-- proof
  apply StatMech.TwoDim.rectangle_finite a b

/--
[mem_leftSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/Crossings.lean)
-/
@[path]
private lemma mem_leftSide_eq
  {a b : ℤ}
  {x : Site 2} :
-- imply
  x ∈ leftSide a b ↔ x ∈ rectangle a b ∧ x 0 = 0 := by
-- proof
  apply StatMech.TwoDim.mem_leftSide

/--
[mem_rightSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/Crossings.lean)
-/
@[path]
private lemma mem_rightSide_eq
  {a b : ℤ}
  {x : Site 2} :
-- imply
  x ∈ rightSide a b ↔ x ∈ rectangle a b ∧ x 0 = a := by
-- proof
  apply StatMech.TwoDim.mem_rightSide

/--
[mem_bottomSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/Crossings.lean)
-/
@[path]
private lemma mem_bottomSide_eq
  {a b : ℤ}
  {x : Site 2} :
-- imply
  x ∈ bottomSide a b ↔ x ∈ rectangle a b ∧ x 1 = 0 := by
-- proof
  apply StatMech.TwoDim.mem_bottomSide

/--
[mem_topSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/Crossings.lean)
-/
@[path]
private lemma mem_topSide_eq
  {a b : ℤ}
  {x : Site 2} :
-- imply
  x ∈ topSide a b ↔ x ∈ rectangle a b ∧ x 1 = b := by
-- proof
  apply StatMech.TwoDim.mem_topSide

/--
[leftSide_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/Crossings.lean)
-/
@[path]
private lemma leftSide_subset_eq
  {a b : ℤ} :
-- imply
  leftSide a b ⊆ rectangle a b := by
-- proof
  apply StatMech.TwoDim.leftSide_subset

/--
[rightSide_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/Crossings.lean)
-/
@[path]
private lemma rightSide_subset_eq
  {a b : ℤ} :
-- imply
  rightSide a b ⊆ rectangle a b := by
-- proof
  apply StatMech.TwoDim.rightSide_subset

/--
[bottomSide_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/Crossings.lean)
-/
@[path]
private lemma bottomSide_subset_eq
  {a b : ℤ} :
-- imply
  bottomSide a b ⊆ rectangle a b := by
-- proof
  apply StatMech.TwoDim.bottomSide_subset

/--
[topSide_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/Crossings.lean)
-/
@[path]
private lemma topSide_subset_eq
  {a b : ℤ} :
-- imply
  topSide a b ⊆ rectangle a b := by
-- proof
  apply StatMech.TwoDim.topSide_subset

/--
[mem_horizontalCrossingEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/Crossings.lean)
-/
@[path]
private lemma mem_horizontalCrossingEvent_eq
  {a b : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  ω ∈ horizontalCrossingEvent a b ↔ HorizontalCrossing ω a b := by
-- proof
  apply StatMech.TwoDim.mem_horizontalCrossingEvent

/--
[mem_verticalCrossingEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/Crossings.lean)
-/
@[path]
private lemma mem_verticalCrossingEvent_eq
  {a b : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  ω ∈ verticalCrossingEvent a b ↔ VerticalCrossing ω a b := by
-- proof
  apply StatMech.TwoDim.mem_verticalCrossingEvent

/--
[HorizontalCrossing.connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/Crossings.lean)
-/
@[path]
private lemma connected_eq
  {a b : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : HorizontalCrossing ω a b) :
-- imply
  ∃ (x y : Site 2), x ∈ leftSide a b ∧ y ∈ rightSide a b ∧ Connected 2 ω x y := by
-- proof
  apply StatMech.TwoDim.HorizontalCrossing.connected h

/--
[VerticalCrossing.connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/Crossings.lean)
-/
@[path]
private lemma connected_eq_2
  {a b : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : VerticalCrossing ω a b) :
-- imply
  ∃ (x y : Site 2), x ∈ bottomSide a b ∧ y ∈ topSide a b ∧ Connected 2 ω x y := by
-- proof
  apply StatMech.TwoDim.VerticalCrossing.connected h

/--
[openSubgraph_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/Crossings.lean)
-/
@[path]
private lemma openSubgraph_mono_eq
  {a b : ℤ}
  {ω ω' : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : ω ≤ ω') :
-- imply
  openSubgraph 2 ω ≤ openSubgraph 2 ω' := by
-- proof
  apply StatMech.TwoDim.openSubgraph_mono h

/--
[connectedWithin_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/Crossings.lean)
-/
@[path]
private lemma connectedWithin_mono_eq
  {a b : ℤ}
  {ω ω' : ConfigSpace (Sym2 (Site 2))}
  {S : Set (Site 2)}
  {x y : S}
-- given
  (h : ω ≤ ω')
  (hxy : ConnectedWithin 2 ω S x y) :
-- imply
  ConnectedWithin 2 ω' S x y := by
-- proof
  apply StatMech.TwoDim.connectedWithin_mono h hxy

/--
[horizontalCrossingEvent_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/Crossings.lean)
-/
@[path]
private lemma horizontalCrossingEvent_increasing_eq
  {a b : ℤ}
  {ω ω' : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : ω ≤ ω')
  (hω : ω ∈ horizontalCrossingEvent a b) :
-- imply
  ω' ∈ horizontalCrossingEvent a b := by
-- proof
  apply StatMech.TwoDim.horizontalCrossingEvent_increasing h hω

/--
[verticalCrossingEvent_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/Crossings.lean)
-/
@[path]
private lemma verticalCrossingEvent_increasing_eq
  {a b : ℤ}
  {ω ω' : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : ω ≤ ω')
  (hω : ω ∈ verticalCrossingEvent a b) :
-- imply
  ω' ∈ verticalCrossingEvent a b := by
-- proof
  apply StatMech.TwoDim.verticalCrossingEvent_increasing h hω


-- created on 2026-10-23
