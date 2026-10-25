import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.RowLinkedClose.Part5
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[rlc_rayCount_zero_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RowLinkedClose.lean)
-/
@[path]
private lemma rlc_rayCount_zero_left_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (h : ∀ p ∈ w.support, z 0 ≤ p 0) :
-- imply
  jec_rayCount z w = 0 := by
-- proof
  apply StatMech.Lattice.rlc_rayCount_zero_left z w h

/--
[rlc_rayCount_zero_below](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RowLinkedClose.lean)
-/
@[path]
private lemma rlc_rayCount_zero_below_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (h : ∀ p ∈ w.support, z 1 ≤ p 1) :
-- imply
  jec_rayCount z w = 0 := by
-- proof
  apply StatMech.Lattice.rlc_rayCount_zero_below z w h

/--
[rlc_rayCount_zero_above](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RowLinkedClose.lean)
-/
@[path]
private lemma rlc_rayCount_zero_above_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (h : ∀ p ∈ w.support, p 1 ≤ z 1 - 1) :
-- imply
  jec_rayCount z w = 0 := by
-- proof
  apply StatMech.Lattice.rlc_rayCount_zero_above z w h

/--
[rlc_support_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RowLinkedClose.lean)
-/
@[path]
private lemma rlc_support_bound_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a} :
-- imply
  ∃ M : ℤ, ∀ p ∈ Vc.support, := by
-- proof
  apply StatMech.Lattice.rlc_support_bound Vc

/--
[rlc_interior_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RowLinkedClose.lean)
-/
@[path]
private lemma rlc_interior_bounded_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a} :
-- imply
  ∃ M : ℤ, ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M) := by
-- proof
  apply StatMech.Lattice.rlc_interior_bounded Vc

/--
[rlc_offSupportInterior_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RowLinkedClose.lean)
-/
@[path]
private lemma rlc_offSupportInterior_finite_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a} :
-- imply
  (jil_offSupportInterior Vc).Finite := by
-- proof
  apply StatMech.Lattice.rlc_offSupportInterior_finite Vc

/--
[rlc_lexMeasure_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RowLinkedClose.lean)
-/
@[path]
private lemma rlc_lexMeasure_lt_eq
  {M : ℤ}
  {z z' : Site 2}
-- given
  (hz0 : -M < z 0)
  (hz0' : z 0 ≤ M)
  (hz1 : -M < z 1)
  (hz1' : z 1 ≤ M)
  (hz'0 : -M < z' 0)
  (hz'0' : z' 0 ≤ M)
  (hz'1 : -M < z' 1)
  (_hz'1' : z' 1 ≤ M)
  (hlex : z' 1 < z 1 ∨ (z' 1 = z 1 ∧ z' 0 < z 0)) :
-- imply
  rlc_lexMeasure M z' < rlc_lexMeasure M z := by
-- proof
  apply StatMech.Lattice.rlc_lexMeasure_lt hz0 hz0' hz1 hz1' hz'0 hz'0' hz'1 _hz'1' hlex

/--
[rlc_exists_lexMin_seed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RowLinkedClose.lean)
-/
@[path]
private lemma rlc_exists_lexMin_seed_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z₀ : Site 2}
  {M : ℤ}
-- given
  (hz₀ : z₀ ∈ jil_offSupportInterior Vc) :
-- imply
  ∃ seed ∈ jil_offSupportInterior Vc, ∀ z ∈ jil_offSupportInterior Vc, rlc_lexMeasure M seed ≤ rlc_lexMeasure M z := by
-- proof
  apply StatMech.Lattice.rlc_exists_lexMin_seed Vc hz₀ M

/--
[rlc_down_mem_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RowLinkedClose.lean)
-/
@[path]
private lemma rlc_down_mem_interior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : ℤ}
-- given
  (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
  (hdown : (![x, y - 1] : Site 2) ∉ Vc.support) :
-- imply
  (![x, y - 1] : Site 2) ∈ jil_offSupportInterior Vc := by
-- proof
  apply StatMech.Lattice.rlc_down_mem_interior Vc hz hdown

/--
[rlc_left_mem_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RowLinkedClose.lean)
-/
@[path]
private lemma rlc_left_mem_interior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : ℤ}
-- given
  (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
  (hleft : (![x - 1, y] : Site 2) ∉ Vc.support) :
-- imply
  (![x - 1, y] : Site 2) ∈ jil_offSupportInterior Vc := by
-- proof
  apply StatMech.Lattice.rlc_left_mem_interior Vc hz hleft

/--
[rlc_descend_via_leftStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RowLinkedClose.lean)
-/
@[path]
private lemma rlc_descend_via_leftStep_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {M : ℤ}
  {x y : ℤ}
-- given
  (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
  (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
  (hleft : (![x - 1, y] : Site 2) ∉ Vc.support) :
-- imply
  ∃ z' ∈ jil_offSupportInterior Vc, rlc_lexMeasure M z' < rlc_lexMeasure M (![x, y] : Site 2) ∧ ∃ p : (hypercubicLattice 2).Walk (![x, y] : Site 2) z', ∀ w ∈ p.support, w ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.rlc_descend_via_leftStep Vc M hMb hz hleft

/--
[rlc_descend_via_downStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RowLinkedClose.lean)
-/
@[path]
private lemma rlc_descend_via_downStep_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {M : ℤ}
  {x y cx : ℤ}
  {preach : (hypercubicLattice 2).Walk (![x, y] : Site 2) ![cx, y]}
-- given
  (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
  (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
  (hpreach : ∀ w ∈ preach.support, w ∉ Vc.support)
  (hc : (![cx, y] : Site 2) ∈ jil_offSupportInterior Vc)
  (hcdown : (![cx, y - 1] : Site 2) ∉ Vc.support) :
-- imply
  ∃ z' ∈ jil_offSupportInterior Vc, rlc_lexMeasure M z' < rlc_lexMeasure M (![x, y] : Site 2) ∧ ∃ p : (hypercubicLattice 2).Walk (![x, y] : Site 2) z', ∀ w ∈ p.support, w ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.rlc_descend_via_downStep Vc M hMb hz preach hpreach hc hcdown

/--
[rlc_descend_via_segmentDown](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RowLinkedClose.lean)
-/
@[path]
private lemma rlc_descend_via_segmentDown_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {M : ℤ}
  {x y cx : ℤ}
-- given
  (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
  (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
  (hxcx : x ≤ cx)
  (hrun : ∀ t : ℤ, x ≤ t → t ≤ cx → (![t, y] : Site 2) ∉ Vc.support)
  (hcdown : (![cx, y - 1] : Site 2) ∉ Vc.support) :
-- imply
  ∃ z' ∈ jil_offSupportInterior Vc, rlc_lexMeasure M z' < rlc_lexMeasure M (![x, y] : Site 2) ∧ ∃ p : (hypercubicLattice 2).Walk (![x, y] : Site 2) z', ∀ w ∈ p.support, w ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.rlc_descend_via_segmentDown Vc M hMb hz hxcx hrun hcdown

/--
[rlc_downLink_of_leftEndDescends](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RowLinkedClose.lean)
-/
@[path]
private lemma rlc_downLink_of_leftEndDescends_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
  {M : ℤ}
-- given
  (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
  (hres : rlc_LeftEndDescends Vc seed M) :
-- imply
  rlc_DownLink Vc seed M := by
-- proof
  apply StatMech.Lattice.rlc_downLink_of_leftEndDescends Vc M hMb hres

/--
[rlc_rowLinked_of_downLink](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RowLinkedClose.lean)
-/
@[path]
private lemma rlc_rowLinked_of_downLink_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
  {M : ℤ}
-- given
  (hdl : rlc_DownLink Vc seed M) :
-- imply
  jil_RowLinked Vc seed := by
-- proof
  apply StatMech.Lattice.rlc_rowLinked_of_downLink Vc M hdl

/--
[rlc_rowLinked_of_leftEndDescends](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RowLinkedClose.lean)
-/
@[path]
private lemma rlc_rowLinked_of_leftEndDescends_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
  {M : ℤ}
-- given
  (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
  (hres : rlc_LeftEndDescends Vc seed M) :
-- imply
  jil_RowLinked Vc seed := by
-- proof
  apply StatMech.Lattice.rlc_rowLinked_of_leftEndDescends Vc M hMb hres

/--
[rlc_leftEndDescends_of_segmentDown](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RowLinkedClose.lean)
-/
@[path]
private lemma rlc_leftEndDescends_of_segmentDown_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
  {M : ℤ}
-- given
  (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
  (hres : rlc_SegmentDown Vc seed) :
-- imply
  rlc_LeftEndDescends Vc seed M := by
-- proof
  apply StatMech.Lattice.rlc_leftEndDescends_of_segmentDown Vc M hMb hres

/--
[rlc_rowLinked_of_segmentDown](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RowLinkedClose.lean)
-/
@[path]
private lemma rlc_rowLinked_of_segmentDown_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
  {M : ℤ}
-- given
  (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
  (hres : rlc_SegmentDown Vc seed) :
-- imply
  jil_RowLinked Vc seed := by
-- proof
  apply StatMech.Lattice.rlc_rowLinked_of_segmentDown Vc M hMb hres

/--
[rlc_exists_rowLinked_seed_of_segmentDown](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RowLinkedClose.lean)
-/
@[path]
private lemma rlc_exists_rowLinked_seed_of_segmentDown_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z₀ : Site 2}
-- given
  (hz₀ : z₀ ∈ jil_offSupportInterior Vc)
  (hres : ∀ seed : Site 2, rlc_SegmentDown Vc seed) :
-- imply
  ∃ seed ∈ jil_offSupportInterior Vc, jil_RowLinked Vc seed := by
-- proof
  apply StatMech.Lattice.rlc_exists_rowLinked_seed_of_segmentDown Vc hz₀ hres

/--
[rlc_segmentDown_body_of_downOffSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RowLinkedClose.lean)
-/
@[path]
private lemma rlc_segmentDown_body_of_downOffSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hzoff : z ∉ Vc.support)
  (hdown : (![z 0, z 1 - 1] : Site 2) ∉ Vc.support) :
-- imply
  ∃ cx : ℤ, z 0 ≤ cx ∧ (∀ t : ℤ, z 0 ≤ t → t ≤ cx → (![t, z 1] : Site 2) ∉ Vc.support) ∧ (![cx, z 1 - 1] : Site 2) ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.rlc_segmentDown_body_of_downOffSupport Vc hzoff hdown

/--
[rlc_segmentDown_of_downOffSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RowLinkedClose.lean)
-/
@[path]
private lemma rlc_segmentDown_of_downOffSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hdown : ∀ z ∈ jil_offSupportInterior Vc, z ≠ seed → (![z 0 - 1, z 1] : Site 2) ∈ Vc.support → (![z 0, z 1 - 1] : Site 2) ∉ Vc.support) :
-- imply
  rlc_SegmentDown Vc seed := by
-- proof
  apply StatMech.Lattice.rlc_segmentDown_of_downOffSupport Vc seed hdown

/--
[rlc_segmentDown_body_multiCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RowLinkedClose.lean)
-/
@[path]
private lemma rlc_segmentDown_body_multiCell_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z0 z1 : ℤ}
-- given
  (h0 : (![z0, z1] : Site 2) ∉ Vc.support)
  (h1 : (![z0 + 1, z1] : Site 2) ∉ Vc.support)
  (hd : (![z0 + 1, z1 - 1] : Site 2) ∉ Vc.support) :
-- imply
  ∃ cx : ℤ, z0 < cx ∧ (∀ t : ℤ, z0 ≤ t → t ≤ cx → (![t, z1] : Site 2) ∉ Vc.support) ∧ (![cx, z1 - 1] : Site 2) ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.rlc_segmentDown_body_multiCell Vc h0 h1 hd

/--
[rlc_downLink_witness_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RowLinkedClose.lean)
-/
@[path]
private lemma rlc_downLink_witness_ne_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
  {M : ℤ}
  {z : Site 2}
-- given
  (hdl : rlc_DownLink Vc seed M)
  (hz : z ∈ jil_offSupportInterior Vc)
  (hzs : z ≠ seed) :
-- imply
  ∃ z' ∈ jil_offSupportInterior Vc, z' ≠ z ∧ ∃ p : (hypercubicLattice 2).Walk z z', ∀ w ∈ p.support, w ∉ Vc.support := by
-- proof
  apply StatMech.Lattice.rlc_downLink_witness_ne Vc M hdl hz hzs


-- created on 2026-10-23
