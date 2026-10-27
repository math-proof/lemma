import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.GlobalThickPointClose.Part2
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[gtp_thickPoint_of_adj_horiz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GlobalThickPointClose.lean)
-/
@[path]
private lemma gtp_thickPoint_of_adj_horiz_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : ℤ}
-- given
  (h0 : (![x, y] : Site 2) ∈ Vc.support)
  (h1 : (![x + 1, y] : Site 2) ∈ Vc.support)
  (hne : s((![x, y] : Site 2), (![x + 1, y] : Site 2)) ∉ Vc.edges) :
-- imply
  kns_ThickPoint Vc := by
-- proof
  apply StatMech.Lattice.gtp_thickPoint_of_adj_horiz Vc h0 h1 hne

/--
[gtp_thickPoint_of_adj_vert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GlobalThickPointClose.lean)
-/
@[path]
private lemma gtp_thickPoint_of_adj_vert_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : ℤ}
-- given
  (h0 : (![x, y] : Site 2) ∈ Vc.support)
  (h1 : (![x, y + 1] : Site 2) ∈ Vc.support)
  (hne : s((![x, y] : Site 2), (![x, y + 1] : Site 2)) ∉ Vc.edges) :
-- imply
  kns_ThickPoint Vc := by
-- proof
  apply StatMech.Lattice.gtp_thickPoint_of_adj_vert Vc h0 h1 hne

/--
[gtp_edge_or_thick_horiz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GlobalThickPointClose.lean)
-/
@[path]
private lemma gtp_edge_or_thick_horiz_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : ℤ}
-- given
  (h0 : (![x, y] : Site 2) ∈ Vc.support)
  (h1 : (![x + 1, y] : Site 2) ∈ Vc.support) :
-- imply
  s((![x, y] : Site 2), (![x + 1, y] : Site 2)) ∈ Vc.edges ∨ kns_ThickPoint Vc := by
-- proof
  apply StatMech.Lattice.gtp_edge_or_thick_horiz Vc h0 h1

/--
[gtp_edge_or_thick_vert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GlobalThickPointClose.lean)
-/
@[path]
private lemma gtp_edge_or_thick_vert_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : ℤ}
-- given
  (h0 : (![x, y] : Site 2) ∈ Vc.support)
  (h1 : (![x, y + 1] : Site 2) ∈ Vc.support) :
-- imply
  s((![x, y] : Site 2), (![x, y + 1] : Site 2)) ∈ Vc.edges ∨ kns_ThickPoint Vc := by
-- proof
  apply StatMech.Lattice.gtp_edge_or_thick_vert Vc h0 h1

/--
[gtp_eastBoundary_onSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GlobalThickPointClose.lean)
-/
@[path]
private lemma gtp_eastBoundary_onSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {q : Site 2}
-- given
  (hqI : q ∈ jil_offSupportInterior Vc) :
-- imply
  ∃ e : ℤ, q 0 < e ∧ (![e, q 1] : Site 2) ∈ Vc.support ∧ ∀ x : ℤ, q 0 ≤ x → x < e → (![x, q 1] : Site 2) ∈ jil_offSupportInterior Vc := by
-- proof
  apply StatMech.Lattice.gtp_eastBoundary_onSupport Vc hqI

/--
[gtp_runEnd_bottomCorner_onSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GlobalThickPointClose.lean)
-/
@[path]
private lemma gtp_runEnd_bottomCorner_onSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {T : Set (Site 2)}
  {q : Site 2}
  {M e : ℤ}
-- given
  (hbottom : ∀ wx : ℤ, (-M < wx ∧ wx ≤ M) → (![wx, q 1] : Site 2) ∈ jil_offSupportInterior Vc → (![wx, q 1] : Site 2) ∉ T → (![wx, q 1 - 1] : Site 2) ∈ Vc.support)
  (hlastbox : -M < e - 1 ∧ e - 1 ≤ M)
  (hlastI : (![e - 1, q 1] : Site 2) ∈ jil_offSupportInterior Vc)
  (hlastnT : (![e - 1, q 1] : Site 2) ∉ T) :
-- imply
  (![e - 1, q 1 - 1] : Site 2) ∈ Vc.support := by
-- proof
  apply StatMech.Lattice.gtp_runEnd_bottomCorner_onSupport Vc hbottom hlastbox hlastI hlastnT

/--
[gtp_noKingSeparation_of_fourThin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GlobalThickPointClose.lean)
-/
@[path]
private lemma gtp_noKingSeparation_of_fourThin_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseedI : seed ∈ jil_offSupportInterior Vc)
  (hthin : mci_FourThin Vc)
  (hres : gtp_RunEndReconnect Vc seed) :
-- imply
  ksc_NoKingSeparation Vc seed := by
-- proof
  apply StatMech.Lattice.gtp_noKingSeparation_of_fourThin Vc hseedI hthin hres

/--
[gtp_kingRowLinked_of_fourThin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GlobalThickPointClose.lean)
-/
@[path]
private lemma gtp_kingRowLinked_of_fourThin_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseedI : seed ∈ jil_offSupportInterior Vc)
  (hthin : mci_FourThin Vc)
  (hres : gtp_RunEndReconnect Vc seed) :
-- imply
  mci_KingRowLinked Vc seed := by
-- proof
  apply StatMech.Lattice.gtp_kingRowLinked_of_fourThin Vc hseedI hthin hres

/--
[gtp_runEndReconnect_of_escapeWallThick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GlobalThickPointClose.lean)
-/
@[path]
private lemma gtp_runEndReconnect_of_escapeWallThick_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hetp : etp_EscapeWallThick Vc seed) :
-- imply
  gtp_RunEndReconnect Vc seed := by
-- proof
  apply StatMech.Lattice.gtp_runEndReconnect_of_escapeWallThick Vc hetp

/--
[gtp_runEndReconnect_of_bottomWallThick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GlobalThickPointClose.lean)
-/
@[path]
private lemma gtp_runEndReconnect_of_bottomWallThick_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hewt : ewt_BottomWallThick Vc seed) :
-- imply
  gtp_RunEndReconnect Vc seed := by
-- proof
  apply StatMech.Lattice.gtp_runEndReconnect_of_bottomWallThick Vc hewt

/--
[gtp_fjord_runEndReconnect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GlobalThickPointClose.lean)
-/
@[path]
private lemma gtp_fjord_runEndReconnect_eq :
-- imply
  gtp_RunEndReconnect sdc_fjord (![5, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.gtp_fjord_runEndReconnect

/--
[gtp_fjord_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GlobalThickPointClose.lean)
-/
@[path]
private lemma gtp_fjord_nonvacuous_eq :
-- imply
  kns_KingSeparation sdc_fjord (![5, 1] : Site 2) ∧ kns_ThickPoint sdc_fjord ∧ gtp_RunEndReconnect sdc_fjord (![5, 1] : Site 2) ∧ ¬ mci_FourThin sdc_fjord := by
-- proof
  apply StatMech.Lattice.gtp_fjord_nonvacuous

/--
[gtp_ksd_runEndReconnect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GlobalThickPointClose.lean)
-/
@[path]
private lemma gtp_ksd_runEndReconnect_eq :
-- imply
  gtp_RunEndReconnect ksd_stair (![1, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.gtp_ksd_runEndReconnect

/--
[gtp_kda_runEndReconnect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GlobalThickPointClose.lean)
-/
@[path]
private lemma gtp_kda_runEndReconnect_eq :
-- imply
  gtp_RunEndReconnect kda_stairDR (![3, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.gtp_kda_runEndReconnect

/--
[gtp_kingRowLinked_summary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/GlobalThickPointClose.lean)
-/
@[path]
private lemma gtp_kingRowLinked_summary_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseedI : seed ∈ jil_offSupportInterior Vc)
  (hthin : mci_FourThin Vc) :
-- imply
  gtp_RunEndReconnect Vc seed → mci_KingRowLinked Vc seed := by
-- proof
  apply StatMech.Lattice.gtp_kingRowLinked_summary Vc hseedI hthin


-- created on 2026-10-23
