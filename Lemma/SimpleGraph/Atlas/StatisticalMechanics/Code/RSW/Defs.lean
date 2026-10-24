import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.RSW.Defs
open Set StatMech StatMech.RSW StatMech.RSW.Box


/--
[mem_rect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean)
-/
@[path]
private lemma mem_rect_eq
  {a b c d : ℤ}
  {x : Site 2} :
-- imply
  x ∈ rect a b c d ↔ a ≤ x 0 ∧ x 0 ≤ b ∧ c ≤ x 1 ∧ x 1 ≤ d := by
-- proof
  apply StatMech.RSW.Box.mem_rect

/--
[rect_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean)
-/
@[path]
private lemma rect_finite_eq
  {a b c d : ℤ} :
-- imply
  (rect a b c d).Finite := by
-- proof
  apply StatMech.RSW.Box.rect_finite a b c d

/--
[mem_leftSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean)
-/
@[path]
private lemma mem_leftSide_eq
  {a b c d : ℤ}
  {x : Site 2} :
-- imply
  x ∈ leftSide a b c d ↔ x ∈ rect a b c d ∧ x 0 = a := by
-- proof
  apply StatMech.RSW.Box.mem_leftSide

/--
[mem_rightSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean)
-/
@[path]
private lemma mem_rightSide_eq
  {a b c d : ℤ}
  {x : Site 2} :
-- imply
  x ∈ rightSide a b c d ↔ x ∈ rect a b c d ∧ x 0 = b := by
-- proof
  apply StatMech.RSW.Box.mem_rightSide

/--
[mem_bottomSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean)
-/
@[path]
private lemma mem_bottomSide_eq
  {a b c d : ℤ}
  {x : Site 2} :
-- imply
  x ∈ bottomSide a b c d ↔ x ∈ rect a b c d ∧ x 1 = c := by
-- proof
  apply StatMech.RSW.Box.mem_bottomSide

/--
[mem_topSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean)
-/
@[path]
private lemma mem_topSide_eq
  {a b c d : ℤ}
  {x : Site 2} :
-- imply
  x ∈ topSide a b c d ↔ x ∈ rect a b c d ∧ x 1 = d := by
-- proof
  apply StatMech.RSW.Box.mem_topSide

/--
[leftSide_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean)
-/
@[path]
private lemma leftSide_subset_eq
  {a b c d : ℤ} :
-- imply
  leftSide a b c d ⊆ rect a b c d := by
-- proof
  apply StatMech.RSW.Box.leftSide_subset

/--
[rightSide_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean)
-/
@[path]
private lemma rightSide_subset_eq
  {a b c d : ℤ} :
-- imply
  rightSide a b c d ⊆ rect a b c d := by
-- proof
  apply StatMech.RSW.Box.rightSide_subset

/--
[bottomSide_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean)
-/
@[path]
private lemma bottomSide_subset_eq
  {a b c d : ℤ} :
-- imply
  bottomSide a b c d ⊆ rect a b c d := by
-- proof
  apply StatMech.RSW.Box.bottomSide_subset

/--
[topSide_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean)
-/
@[path]
private lemma topSide_subset_eq
  {a b c d : ℤ} :
-- imply
  topSide a b c d ⊆ rect a b c d := by
-- proof
  apply StatMech.RSW.Box.topSide_subset

/--
[mem_horizontalCrossingEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean)
-/
@[path]
private lemma mem_horizontalCrossingEvent_eq
  {a b c d : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  ω ∈ horizontalCrossingEvent a b c d ↔ HorizontalCrossing ω a b c d := by
-- proof
  apply StatMech.RSW.Box.mem_horizontalCrossingEvent

/--
[mem_verticalCrossingEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean)
-/
@[path]
private lemma mem_verticalCrossingEvent_eq
  {a b c d : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  ω ∈ verticalCrossingEvent a b c d ↔ VerticalCrossing ω a b c d := by
-- proof
  apply StatMech.RSW.Box.mem_verticalCrossingEvent

/--
[HorizontalCrossing.connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean)
-/
@[path]
private lemma connected_eq
  {a b c d : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : HorizontalCrossing ω a b c d) :
-- imply
  ∃ x y : Site 2, x ∈ leftSide a b c d ∧ y ∈ rightSide a b c d ∧ Connected 2 ω x y := by
-- proof
  apply StatMech.RSW.Box.HorizontalCrossing.connected h

/--
[VerticalCrossing.connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean)
-/
@[path]
private lemma connected_eq_2
  {a b c d : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : VerticalCrossing ω a b c d) :
-- imply
  ∃ x y : Site 2, x ∈ bottomSide a b c d ∧ y ∈ topSide a b c d ∧ Connected 2 ω x y := by
-- proof
  apply StatMech.RSW.Box.VerticalCrossing.connected h

/--
[horizontalCrossingEvent_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean)
-/
@[path]
private lemma horizontalCrossingEvent_increasing_eq
  {a b c d : ℤ}
  {ω ω' : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : ω ≤ ω')
  (hω : ω ∈ horizontalCrossingEvent a b c d) :
-- imply
  ω' ∈ horizontalCrossingEvent a b c d := by
-- proof
  apply StatMech.RSW.Box.horizontalCrossingEvent_increasing h hω

/--
[verticalCrossingEvent_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean)
-/
@[path]
private lemma verticalCrossingEvent_increasing_eq
  {a b c d : ℤ}
  {ω ω' : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : ω ≤ ω')
  (hω : ω ∈ verticalCrossingEvent a b c d) :
-- imply
  ω' ∈ verticalCrossingEvent a b c d := by
-- proof
  apply StatMech.RSW.Box.verticalCrossingEvent_increasing h hω

/--
[horizontalCrossing_eq_twoDim](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean)
-/
@[path]
private lemma horizontalCrossing_eq_twoDim_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a b : ℤ} :
-- imply
  HorizontalCrossing ω 0 a 0 b ↔ TwoDim.HorizontalCrossing ω a b := by
-- proof
  apply StatMech.RSW.Box.horizontalCrossing_eq_twoDim ω a b

/--
[mem_dualHorizontalCrossingEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean)
-/
@[path]
private lemma mem_dualHorizontalCrossingEvent_eq
  {a b c d : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  ω ∈ dualHorizontalCrossingEvent a b c d ↔ DualHorizontalCrossing ω a b c d := by
-- proof
  apply StatMech.RSW.Box.mem_dualHorizontalCrossingEvent

/--
[mem_dualVerticalCrossingEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean)
-/
@[path]
private lemma mem_dualVerticalCrossingEvent_eq
  {a b c d : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  ω ∈ dualVerticalCrossingEvent a b c d ↔ DualVerticalCrossing ω a b c d := by
-- proof
  apply StatMech.RSW.Box.mem_dualVerticalCrossingEvent

/--
[dualHorizontalCrossing_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean)
-/
@[path]
private lemma dualHorizontalCrossing_iff_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a b c d : ℤ} :
-- imply
  DualHorizontalCrossing ω a b c d ↔ HorizontalCrossing (dualConfig ω) a b c d := by
-- proof
  apply StatMech.RSW.Box.dualHorizontalCrossing_iff ω a b c d

/--
[dualVerticalCrossing_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean)
-/
@[path]
private lemma dualVerticalCrossing_iff_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a b c d : ℤ} :
-- imply
  DualVerticalCrossing ω a b c d ↔ VerticalCrossing (dualConfig ω) a b c d := by
-- proof
  apply StatMech.RSW.Box.dualVerticalCrossing_iff ω a b c d

/--
[dualHorizontalCrossingEvent_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean)
-/
@[path]
private lemma dualHorizontalCrossingEvent_increasing_eq
  {a b c d : ℤ}
  {ω ω' : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : dualConfig ω ≤ dualConfig ω')
  (hω : ω ∈ dualHorizontalCrossingEvent a b c d) :
-- imply
  ω' ∈ dualHorizontalCrossingEvent a b c d := by
-- proof
  apply StatMech.RSW.Box.dualHorizontalCrossingEvent_increasing h hω

/--
[dualVerticalCrossingEvent_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean)
-/
@[path]
private lemma dualVerticalCrossingEvent_increasing_eq
  {a b c d : ℤ}
  {ω ω' : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : dualConfig ω ≤ dualConfig ω')
  (hω : ω ∈ dualVerticalCrossingEvent a b c d) :
-- imply
  ω' ∈ dualVerticalCrossingEvent a b c d := by
-- proof
  apply StatMech.RSW.Box.dualVerticalCrossingEvent_increasing h hω

/--
[mem_annulus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean)
-/
@[path]
private lemma mem_annulus_eq
  {z x : Site 2}
  {n : ℕ} :
-- imply
  x ∈ annulus z n ↔ ∃ y, (y ∈ box 2 (2 * n) ∧ y ∉ box 2 n) ∧ z + y = x := by
-- proof
  apply StatMech.RSW.Box.mem_annulus

/--
[annulus_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean)
-/
@[path]
private lemma annulus_finite_eq
  {z : Site 2}
  {n : ℕ} :
-- imply
  (annulus z n).Finite := by
-- proof
  apply StatMech.RSW.Box.annulus_finite z n

/--
[annulus_subset_outer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean)
-/
@[path]
private lemma annulus_subset_outer_eq
  {z : Site 2}
  {n : ℕ} :
-- imply
  annulus z n ⊆ (fun x => z + x) '' box 2 (2 * n) := by
-- proof
  apply StatMech.RSW.Box.annulus_subset_outer z n

/--
[mem_annulusCircuitEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean)
-/
@[path]
private lemma mem_annulusCircuitEvent_eq
  {z : Site 2}
  {n : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  ω ∈ annulusCircuitEvent z n ↔ AnnulusCircuit ω z n := by
-- proof
  apply StatMech.RSW.Box.mem_annulusCircuitEvent

/--
[P5c.p5](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean)
-/
@[path]
private lemma p5_eq
  {μ : Ξ → ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ}
  {ξ : Ξ}
-- given
  (h : P5c μ) :
-- imply
  P5 (μ ξ) := by
-- proof
  apply StatMech.RSW.Box.P5c.p5 h ξ


-- created on 2026-10-23
