import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.RSW.Strip
open Set MeasureTheory SimpleGraph StatMech StatMech.RSW StatMech.RSW.Strip


/--
[connectedWithin_mono_set](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Strip.lean)
-/
@[path]
private lemma connectedWithin_mono_set_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {S T : Set (Site d)}
  {x y : S}
-- given
  (hST : S ⊆ T)
  (h : ConnectedWithin d ω S x y) :
-- imply
  ConnectedWithin d ω T ⟨(x : Site d), hST x.2⟩ ⟨(y : Site d), hST y.2⟩ := by
-- proof
  apply StatMech.RSW.Strip.connectedWithin_mono_set ω hST h

/--
[connectedWithin_union_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Strip.lean)
-/
@[path]
private lemma connectedWithin_union_left_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {S T : Set (Site d)}
  {x y : Site d}
-- given
  (hx : x ∈ S)
  (hy : y ∈ S)
  (h : ConnectedWithin d ω S ⟨x, hx⟩ ⟨y, hy⟩) :
-- imply
  ConnectedWithin d ω (S ∪ T) ⟨x, Or.inl hx⟩ ⟨y, Or.inl hy⟩ := by
-- proof
  apply StatMech.RSW.Strip.connectedWithin_union_left ω S T hx hy h

/--
[connectedWithin_union_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Strip.lean)
-/
@[path]
private lemma connectedWithin_union_right_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {S T : Set (Site d)}
  {x y : Site d}
-- given
  (hx : x ∈ T)
  (hy : y ∈ T)
  (h : ConnectedWithin d ω T ⟨x, hx⟩ ⟨y, hy⟩) :
-- imply
  ConnectedWithin d ω (S ∪ T) ⟨x, Or.inr hx⟩ ⟨y, Or.inr hy⟩ := by
-- proof
  apply StatMech.RSW.Strip.connectedWithin_union_right ω S T hx hy h

/--
[connectedWithin_glue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Strip.lean)
-/
@[path]
private lemma connectedWithin_glue_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {S T : Set (Site d)}
  {x z y : Site d}
-- given
  (hxS : x ∈ S)
  (hzS : z ∈ S)
  (hzT : z ∈ T)
  (hyT : y ∈ T)
  (h0 : ConnectedWithin d ω S ⟨x, hxS⟩ ⟨z, hzS⟩)
  (h1 : ConnectedWithin d ω T ⟨z, hzT⟩ ⟨y, hyT⟩) :
-- imply
  ConnectedWithin d ω (S ∪ T) ⟨x, Or.inl hxS⟩ ⟨y, Or.inr hyT⟩ := by
-- proof
  apply StatMech.RSW.Strip.connectedWithin_glue ω S T hxS hzS hzT hyT h0 h1

/--
[rect_subset_of_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Strip.lean)
-/
@[path]
private lemma rect_subset_of_right_eq
  {a m b c d : ℤ}
-- given
  (hmb : m ≤ b) :
-- imply
  rect a m c d ⊆ rect a b c d := by
-- proof
  apply StatMech.RSW.Strip.rect_subset_of_right hmb

/--
[rect_subset_of_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Strip.lean)
-/
@[path]
private lemma rect_subset_of_left_eq
  {a m b c d : ℤ}
-- given
  (ham : a ≤ m) :
-- imply
  rect m b c d ⊆ rect a b c d := by
-- proof
  apply StatMech.RSW.Strip.rect_subset_of_left ham

/--
[rect_subset_of_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Strip.lean)
-/
@[path]
private lemma rect_subset_of_top_eq
  {a b c m d : ℤ}
-- given
  (hmd : m ≤ d) :
-- imply
  rect a b c m ⊆ rect a b c d := by
-- proof
  apply StatMech.RSW.Strip.rect_subset_of_top hmd

/--
[rect_subset_of_bottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Strip.lean)
-/
@[path]
private lemma rect_subset_of_bottom_eq
  {a b c m d : ℤ}
-- given
  (hcm : c ≤ m) :
-- imply
  rect a b m d ⊆ rect a b c d := by
-- proof
  apply StatMech.RSW.Strip.rect_subset_of_bottom hcm

/--
[rect_union_horiz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Strip.lean)
-/
@[path]
private lemma rect_union_horiz_eq
  {a m b c d : ℤ}
-- given
  (ham : a ≤ m)
  (hmb : m ≤ b) :
-- imply
  rect a m c d ∪ rect m b c d = rect a b c d := by
-- proof
  apply StatMech.RSW.Strip.rect_union_horiz ham hmb

/--
[rect_union_vert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Strip.lean)
-/
@[path]
private lemma rect_union_vert_eq
  {a b c m d : ℤ}
-- given
  (hcm : c ≤ m)
  (hmd : m ≤ d) :
-- imply
  rect a b c m ∪ rect a b m d = rect a b c d := by
-- proof
  apply StatMech.RSW.Strip.rect_union_vert hcm hmd

/--
[mem_shared_column](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Strip.lean)
-/
@[path]
private lemma mem_shared_column_eq
  {a m b c d : ℤ}
  {z : Site 2}
-- given
  (ham : a ≤ m)
  (hmb : m ≤ b)
  (hz0 : z 0 = m)
  (hzc : c ≤ z 1)
  (hzd : z 1 ≤ d) :
-- imply
  z ∈ rightSide a m c d ∧ z ∈ leftSide m b c d := by
-- proof
  apply StatMech.RSW.Strip.mem_shared_column ham hmb hz0 hzc hzd

/--
[horizontalCrossing_glue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Strip.lean)
-/
@[path]
private lemma horizontalCrossing_glue_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a m b c d : ℤ}
  {xL : Site 2}
  {p : Site 2}
  {q : Site 2}
  {yR : Site 2}
-- given
  (ham : a ≤ m)
  (hmb : m ≤ b)
  (hxL : xL ∈ leftSide a m c d)
  (hp : p ∈ rightSide a m c d)
  (hc1 : ConnectedWithin 2 ω (rect a m c d) ⟨xL, leftSide_subset hxL⟩ ⟨p, rightSide_subset hp⟩)
  (hq : q ∈ leftSide m b c d)
  (hyR : yR ∈ rightSide m b c d)
  (hc2 : ConnectedWithin 2 ω (rect m b c d) ⟨q, leftSide_subset hq⟩ ⟨yR, rightSide_subset hyR⟩)
  (hglue : ConnectedWithin 2 ω (rect a b c d) ⟨p, rect_subset_of_right hmb (rightSide_subset hp)⟩ ⟨q, rect_subset_of_left ham (leftSide_subset hq)⟩) :
-- imply
  HorizontalCrossing ω a b c d := by
-- proof
  apply StatMech.RSW.Strip.horizontalCrossing_glue ham hmb hxL hp hc1 hq hyR hc2 hglue

/--
[horizontalCrossing_glue_of_meet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Strip.lean)
-/
@[path]
private lemma horizontalCrossing_glue_of_meet_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a m b c d : ℤ}
  {xL : Site 2}
  {z : Site 2}
  {yR : Site 2}
-- given
  (ham : a ≤ m)
  (hmb : m ≤ b)
  (hxL : xL ∈ leftSide a m c d)
  (hz0 : z 0 = m)
  (hzc : c ≤ z 1)
  (hzd : z 1 ≤ d)
  (hc1 : ConnectedWithin 2 ω (rect a m c d) ⟨xL, leftSide_subset hxL⟩ ⟨z, rightSide_subset (mem_shared_column ham hmb hz0 hzc hzd).1⟩)
  (hyR : yR ∈ rightSide m b c d)
  (hc2 : ConnectedWithin 2 ω (rect m b c d) ⟨z, leftSide_subset (mem_shared_column ham hmb hz0 hzc hzd).2⟩ ⟨yR, rightSide_subset hyR⟩) :
-- imply
  HorizontalCrossing ω a b c d := by
-- proof
  apply StatMech.RSW.Strip.horizontalCrossing_glue_of_meet ham hmb hxL hz0 hzc hzd hc1 hyR hc2

/--
[mem_shared_row](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Strip.lean)
-/
@[path]
private lemma mem_shared_row_eq
  {a b c m d : ℤ}
  {z : Site 2}
-- given
  (hcm : c ≤ m)
  (hmd : m ≤ d)
  (hz1 : z 1 = m)
  (hza : a ≤ z 0)
  (hzb : z 0 ≤ b) :
-- imply
  z ∈ topSide a b c m ∧ z ∈ bottomSide a b m d := by
-- proof
  apply StatMech.RSW.Strip.mem_shared_row hcm hmd hz1 hza hzb

/--
[verticalCrossing_glue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Strip.lean)
-/
@[path]
private lemma verticalCrossing_glue_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a b c m d : ℤ}
  {xB : Site 2}
  {p : Site 2}
  {q : Site 2}
  {yT : Site 2}
-- given
  (hcm : c ≤ m)
  (hmd : m ≤ d)
  (hxB : xB ∈ bottomSide a b c m)
  (hp : p ∈ topSide a b c m)
  (hc1 : ConnectedWithin 2 ω (rect a b c m) ⟨xB, bottomSide_subset hxB⟩ ⟨p, topSide_subset hp⟩)
  (hq : q ∈ bottomSide a b m d)
  (hyT : yT ∈ topSide a b m d)
  (hc2 : ConnectedWithin 2 ω (rect a b m d) ⟨q, bottomSide_subset hq⟩ ⟨yT, topSide_subset hyT⟩)
  (hglue : ConnectedWithin 2 ω (rect a b c d) ⟨p, rect_subset_of_top hmd (topSide_subset hp)⟩ ⟨q, rect_subset_of_bottom hcm (bottomSide_subset hq)⟩) :
-- imply
  VerticalCrossing ω a b c d := by
-- proof
  apply StatMech.RSW.Strip.verticalCrossing_glue hcm hmd hxB hp hc1 hq hyT hc2 hglue

/--
[verticalCrossing_glue_of_meet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Strip.lean)
-/
@[path]
private lemma verticalCrossing_glue_of_meet_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a b c m d : ℤ}
  {xB : Site 2}
  {z : Site 2}
  {yT : Site 2}
-- given
  (hcm : c ≤ m)
  (hmd : m ≤ d)
  (hxB : xB ∈ bottomSide a b c m)
  (hz1 : z 1 = m)
  (hza : a ≤ z 0)
  (hzb : z 0 ≤ b)
  (hc1 : ConnectedWithin 2 ω (rect a b c m) ⟨xB, bottomSide_subset hxB⟩ ⟨z, topSide_subset (mem_shared_row hcm hmd hz1 hza hzb).1⟩)
  (hyT : yT ∈ topSide a b m d)
  (hc2 : ConnectedWithin 2 ω (rect a b m d) ⟨z, bottomSide_subset (mem_shared_row hcm hmd hz1 hza hzb).2⟩ ⟨yT, topSide_subset hyT⟩) :
-- imply
  VerticalCrossing ω a b c d := by
-- proof
  apply StatMech.RSW.Strip.verticalCrossing_glue_of_meet hcm hmd hxB hz1 hza hzb hc1 hyT hc2

/--
[horizontalCrossingEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Strip.lean)
-/
@[path]
private lemma horizontalCrossingEvent_isIncreasing_eq
  {a b c d : ℤ} :
-- imply
  IsIncreasing (horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.RSW.Strip.horizontalCrossingEvent_isIncreasing a b c d

/--
[verticalCrossingEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Strip.lean)
-/
@[path]
private lemma verticalCrossingEvent_isIncreasing_eq
  {a b c d : ℤ} :
-- imply
  IsIncreasing (verticalCrossingEvent a b c d) := by
-- proof
  apply StatMech.RSW.Strip.verticalCrossingEvent_isIncreasing a b c d

/--
[measureReal_glue_ge_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Strip.lean)
-/
@[path]
private lemma measureReal_glue_ge_mul_eq
  {μ : Measure (ConfigSpace E)}
  [IsFiniteMeasure μ]
  {A B C : Set (ConfigSpace E)}
-- given
  (hpa : PositivelyAssociated μ)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B)
  (hsub : A ∩ B ⊆ C) :
-- imply
  μ.real A * μ.real B ≤ μ.real C := by
-- proof
  apply StatMech.RSW.Strip.measureReal_glue_ge_mul μ hpa hA hB hsub

/--
[measureReal_crossing_product_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Strip.lean)
-/
@[path]
private lemma measureReal_crossing_product_le_eq
  {μ : Measure (ConfigSpace E)}
  [IsFiniteMeasure μ]
  {A C : Set (ConfigSpace E)}
-- given
  (hpa : PositivelyAssociated μ)
  (hA : IsIncreasing A)
  (hsub : A ∩ A ⊆ C) :
-- imply
  μ.real A * μ.real A ≤ μ.real C := by
-- proof
  apply StatMech.RSW.Strip.measureReal_crossing_product_le μ hpa hA hsub

/--
[leftHalfCrossingEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Strip.lean)
-/
@[path]
private lemma leftHalfCrossingEvent_isIncreasing_eq
  {a m c d : ℤ}
  {z : Site 2}
-- given
  (hz : z ∈ rect a m c d) :
-- imply
  IsIncreasing (leftHalfCrossingEvent a m c d z hz) := by
-- proof
  apply StatMech.RSW.Strip.leftHalfCrossingEvent_isIncreasing a m c d z hz

/--
[rightHalfCrossingEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Strip.lean)
-/
@[path]
private lemma rightHalfCrossingEvent_isIncreasing_eq
  {m b c d : ℤ}
  {z : Site 2}
-- given
  (hz : z ∈ rect m b c d) :
-- imply
  IsIncreasing (rightHalfCrossingEvent m b c d z hz) := by
-- proof
  apply StatMech.RSW.Strip.rightHalfCrossingEvent_isIncreasing m b c d z hz

/--
[halfCrossing_glue_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Strip.lean)
-/
@[path]
private lemma halfCrossing_glue_subset_eq
  {a m b c d : ℤ}
  {z : Site 2}
-- given
  (ham : a ≤ m)
  (hmb : m ≤ b)
  (hz0 : z 0 = m)
  (hzc : c ≤ z 1)
  (hzd : z 1 ≤ d) :
-- imply
  leftHalfCrossingEvent a m c d z (rightSide_subset (mem_shared_column ham hmb hz0 hzc hzd).1) ∩ rightHalfCrossingEvent m b c d z (leftSide_subset (mem_shared_column ham hmb hz0 hzc hzd).2) ⊆ horizontalCrossingEvent a b c d := by
-- proof
  apply StatMech.RSW.Strip.halfCrossing_glue_subset ham hmb hz0 hzc hzd

/--
[measureReal_horizontalCrossing_ge_halves](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Strip.lean)
-/
@[path]
private lemma measureReal_horizontalCrossing_ge_halves_eq
  {a m b c d : ℤ}
  {z : Site 2}
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsFiniteMeasure μ]
-- given
  (ham : a ≤ m)
  (hmb : m ≤ b)
  (hz0 : z 0 = m)
  (hzc : c ≤ z 1)
  (hzd : z 1 ≤ d)
  (hpa : PositivelyAssociated μ) :
-- imply
  μ.real (leftHalfCrossingEvent a m c d z (rightSide_subset (mem_shared_column ham hmb hz0 hzc hzd).1)) * μ.real (rightHalfCrossingEvent m b c d z (leftSide_subset (mem_shared_column ham hmb hz0 hzc hzd).2)) ≤ μ.real (horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.RSW.Strip.measureReal_horizontalCrossing_ge_halves ham hmb hz0 hzc hzd μ hpa

/--
[measureReal_chain_ge_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Strip.lean)
-/
@[path]
private lemma measureReal_chain_ge_prod_eq
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  {s : Finset ι}
  {A : ι → Set (ConfigSpace E)}
  {C : Set (ConfigSpace E)}
-- given
  (hpa : PositivelyAssociated μ)
  (hA : ∀ i, IsIncreasing (A i))
  (hsub : (⋂ i ∈ s, A i) ⊆ C) :
-- imply
  (∏ i ∈ s, μ.real (A i)) ≤ μ.real C := by
-- proof
  apply StatMech.RSW.Strip.measureReal_chain_ge_prod μ hpa s hA hsub


-- created on 2026-10-23
