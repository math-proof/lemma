import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.KingInteriorFloodClose
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[kif_kingAdj_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingInteriorFloodClose.lean)
-/
@[path]
private lemma kif_kingAdj_left_eq
  {x y : ℤ} :
-- imply
  mci_kingGraph.Adj (![x, y] : Site 2) ![x - 1, y] := by
-- proof
  apply StatMech.Lattice.kif_kingAdj_left x y

/--
[kif_kingAdj_down](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingInteriorFloodClose.lean)
-/
@[path]
private lemma kif_kingAdj_down_eq
  {x y : ℤ} :
-- imply
  mci_kingGraph.Adj (![x, y] : Site 2) ![x, y - 1] := by
-- proof
  apply StatMech.Lattice.kif_kingAdj_down x y

/--
[kif_kingAdj_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingInteriorFloodClose.lean)
-/
@[path]
private lemma kif_kingAdj_right_eq
  {x y : ℤ} :
-- imply
  mci_kingGraph.Adj (![x, y] : Site 2) ![x + 1, y] := by
-- proof
  apply StatMech.Lattice.kif_kingAdj_right x y

/--
[kif_kingRowLinked_of_kingDownLink](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingInteriorFloodClose.lean)
-/
@[path]
private lemma kif_kingRowLinked_of_kingDownLink_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
  {M : ℤ}
-- given
  (hdl : kif_KingDownLink Vc seed M) :
-- imply
  mci_KingRowLinked Vc seed := by
-- proof
  apply StatMech.Lattice.kif_kingRowLinked_of_kingDownLink Vc M hdl

/--
[kif_descend_via_leftStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingInteriorFloodClose.lean)
-/
@[path]
private lemma kif_descend_via_leftStep_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {M : ℤ}
  {x y : ℤ}
-- given
  (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
  (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
  (hleft : (![x - 1, y] : Site 2) ∉ Vc.support) :
-- imply
  ∃ z' ∈ jil_offSupportInterior Vc, rlc_lexMeasure M z' < rlc_lexMeasure M (![x, y] : Site 2) ∧ ∃ p : mci_kingGraph.Walk (![x, y] : Site 2) z', ∀ w ∈ p.support, w ∈ jil_offSupportInterior Vc := by
-- proof
  apply StatMech.Lattice.kif_descend_via_leftStep Vc M hMb hz hleft

/--
[kif_descend_via_downStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingInteriorFloodClose.lean)
-/
@[path]
private lemma kif_descend_via_downStep_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {M : ℤ}
  {x y : ℤ}
-- given
  (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
  (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
  (hdown : (![x, y - 1] : Site 2) ∉ Vc.support) :
-- imply
  ∃ z' ∈ jil_offSupportInterior Vc, rlc_lexMeasure M z' < rlc_lexMeasure M (![x, y] : Site 2) ∧ ∃ p : mci_kingGraph.Walk (![x, y] : Site 2) z', ∀ w ∈ p.support, w ∈ jil_offSupportInterior Vc := by
-- proof
  apply StatMech.Lattice.kif_descend_via_downStep Vc M hMb hz hdown

/--
[kif_descend_via_diagDR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingInteriorFloodClose.lean)
-/
@[path]
private lemma kif_descend_via_diagDR_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {M : ℤ}
  {x y : ℤ}
-- given
  (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
  (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
  (helbow : (![x + 1, y] : Site 2) ∉ Vc.support)
  (hdiag : (![x + 1, y - 1] : Site 2) ∉ Vc.support) :
-- imply
  ∃ z' ∈ jil_offSupportInterior Vc, rlc_lexMeasure M z' < rlc_lexMeasure M (![x, y] : Site 2) ∧ ∃ p : mci_kingGraph.Walk (![x, y] : Site 2) z', ∀ w ∈ p.support, w ∈ jil_offSupportInterior Vc := by
-- proof
  apply StatMech.Lattice.kif_descend_via_diagDR Vc M hMb hz helbow hdiag

/--
[kif_run_kingWalk_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingInteriorFloodClose.lean)
-/
@[path]
private lemma kif_run_kingWalk_interior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y cx : ℤ}
-- given
  (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
  (hxcx : x ≤ cx)
  (hrun : ∀ t : ℤ, x ≤ t → t ≤ cx → (![t, y] : Site 2) ∉ Vc.support) :
-- imply
  ∃ p : mci_kingGraph.Walk (![x, y] : Site 2) ![cx, y], ∀ w ∈ p.support, w ∈ jil_offSupportInterior Vc := by
-- proof
  apply StatMech.Lattice.kif_run_kingWalk_interior Vc hz hxcx hrun

/--
[kif_descend_via_segmentDown](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingInteriorFloodClose.lean)
-/
@[path]
private lemma kif_descend_via_segmentDown_eq
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
  ∃ z' ∈ jil_offSupportInterior Vc, rlc_lexMeasure M z' < rlc_lexMeasure M (![x, y] : Site 2) ∧ ∃ p : mci_kingGraph.Walk (![x, y] : Site 2) z', ∀ w ∈ p.support, w ∈ jil_offSupportInterior Vc := by
-- proof
  apply StatMech.Lattice.kif_descend_via_segmentDown Vc M hMb hz hxcx hrun hcdown

/--
[kif_descend_via_segmentDiagDR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingInteriorFloodClose.lean)
-/
@[path]
private lemma kif_descend_via_segmentDiagDR_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {M : ℤ}
  {x y cx : ℤ}
-- given
  (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
  (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
  (hxcx : x ≤ cx)
  (hrun : ∀ t : ℤ, x ≤ t → t ≤ cx → (![t, y] : Site 2) ∉ Vc.support)
  (helbow : (![cx + 1, y] : Site 2) ∉ Vc.support)
  (hdiag : (![cx + 1, y - 1] : Site 2) ∉ Vc.support) :
-- imply
  ∃ z' ∈ jil_offSupportInterior Vc, rlc_lexMeasure M z' < rlc_lexMeasure M (![x, y] : Site 2) ∧ ∃ p : mci_kingGraph.Walk (![x, y] : Site 2) z', ∀ w ∈ p.support, w ∈ jil_offSupportInterior Vc := by
-- proof
  apply StatMech.Lattice.kif_descend_via_segmentDiagDR Vc M hMb hz hxcx hrun helbow hdiag

/--
[kif_kingDownLink_of_kingSegmentDown](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingInteriorFloodClose.lean)
-/
@[path]
private lemma kif_kingDownLink_of_kingSegmentDown_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
  {M : ℤ}
-- given
  (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
  (hres : kif_KingSegmentDown Vc seed) :
-- imply
  kif_KingDownLink Vc seed M := by
-- proof
  apply StatMech.Lattice.kif_kingDownLink_of_kingSegmentDown Vc M hMb hres

/--
[kif_kingRowLinked_of_kingSegmentDown](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingInteriorFloodClose.lean)
-/
@[path]
private lemma kif_kingRowLinked_of_kingSegmentDown_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
  {M : ℤ}
-- given
  (hMb : ∀ z ∈ jec_leftRegion Vc, (-M < z 0 ∧ z 0 ≤ M) ∧ (-M < z 1 ∧ z 1 ≤ M))
  (hres : kif_KingSegmentDown Vc seed) :
-- imply
  mci_KingRowLinked Vc seed := by
-- proof
  apply StatMech.Lattice.kif_kingRowLinked_of_kingSegmentDown Vc M hMb hres

/--
[kif_kingInteriorConnected_of_kingSegmentDown](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingInteriorFloodClose.lean)
-/
@[path]
private lemma kif_kingInteriorConnected_of_kingSegmentDown_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z₀ : Site 2}
-- given
  (hz₀ : z₀ ∈ jil_offSupportInterior Vc)
  (hres : ∀ seed : Site 2, kif_KingSegmentDown Vc seed) :
-- imply
  mci_KingInteriorConnected Vc := by
-- proof
  apply StatMech.Lattice.kif_kingInteriorConnected_of_kingSegmentDown Vc hz₀ hres

/--
[kif_kingSegmentDown_body_of_downOffSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingInteriorFloodClose.lean)
-/
@[path]
private lemma kif_kingSegmentDown_body_of_downOffSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
-- given
  (hzoff : z ∉ Vc.support)
  (hdown : (![z 0, z 1 - 1] : Site 2) ∉ Vc.support) :
-- imply
  ∃ cx : ℤ, z 0 ≤ cx ∧ (∀ t : ℤ, z 0 ≤ t → t ≤ cx → (![t, z 1] : Site 2) ∉ Vc.support) ∧ ((![cx, z 1 - 1] : Site 2) ∉ Vc.support ∨ ((![cx + 1, z 1] : Site 2) ∉ Vc.support ∧ (![cx + 1, z 1 - 1] : Site 2) ∉ Vc.support)) := by
-- proof
  apply StatMech.Lattice.kif_kingSegmentDown_body_of_downOffSupport Vc hzoff hdown

/--
[kif_kingSegmentDown_body_via_diagDR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingInteriorFloodClose.lean)
-/
@[path]
private lemma kif_kingSegmentDown_body_via_diagDR_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z0 z1 : ℤ}
-- given
  (hzoff : (![z0, z1] : Site 2) ∉ Vc.support)
  (helbow : (![z0 + 1, z1] : Site 2) ∉ Vc.support)
  (hdiag : (![z0 + 1, z1 - 1] : Site 2) ∉ Vc.support) :
-- imply
  ∃ cx : ℤ, z0 ≤ cx ∧ (∀ t : ℤ, z0 ≤ t → t ≤ cx → (![t, z1] : Site 2) ∉ Vc.support) ∧ ((![cx, z1 - 1] : Site 2) ∉ Vc.support ∨ ((![cx + 1, z1] : Site 2) ∉ Vc.support ∧ (![cx + 1, z1 - 1] : Site 2) ∉ Vc.support)) := by
-- proof
  apply StatMech.Lattice.kif_kingSegmentDown_body_via_diagDR Vc hzoff helbow hdiag

/--
[kif_fjord_on_70](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingInteriorFloodClose.lean)
-/
@[path]
private lemma kif_fjord_on_70_eq :
-- imply
  (![7, 0] : Site 2) ∈ sdc_fjord.support := by
-- proof
  apply StatMech.Lattice.kif_fjord_on_70

/--
[kif_fjord_body_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingInteriorFloodClose.lean)
-/
@[path]
private lemma kif_fjord_body_false_eq :
-- imply
  ¬ ∃ cx : ℤ, (5 : ℤ) ≤ cx ∧ (∀ t : ℤ, (5 : ℤ) ≤ t → t ≤ cx → (![t, 1] : Site 2) ∉ sdc_fjord.support) ∧ ((![cx, 1 - 1] : Site 2) ∉ sdc_fjord.support ∨ ((![cx + 1, 1] : Site 2) ∉ sdc_fjord.support ∧ (![cx + 1, 1 - 1] : Site 2) ∉ sdc_fjord.support)) := by
-- proof
  apply StatMech.Lattice.kif_fjord_body_false

/--
[kif_fjord_kingSegmentDown_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingInteriorFloodClose.lean)
-/
@[path]
private lemma kif_fjord_kingSegmentDown_false_eq :
-- imply
  ∃ (seed : Site 2), seed ∈ jil_offSupportInterior sdc_fjord ∧ ¬ kif_KingSegmentDown sdc_fjord seed := by
-- proof
  apply StatMech.Lattice.kif_fjord_kingSegmentDown_false


-- created on 2026-10-23
