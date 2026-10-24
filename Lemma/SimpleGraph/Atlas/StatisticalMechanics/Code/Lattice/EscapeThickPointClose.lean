import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.EscapeThickPointClose
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[etp_adj_vert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeThickPointClose.lean)
-/
@[path]
private lemma etp_adj_vert_eq
  {x y : ℤ} :
-- imply
  (hypercubicLattice 2).Adj (![x, y] : Site 2) ![x, y + 1] := by
-- proof
  apply StatMech.Lattice.etp_adj_vert x y

/--
[etp_adj_horiz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeThickPointClose.lean)
-/
@[path]
private lemma etp_adj_horiz_eq
  {x y : ℤ} :
-- imply
  (hypercubicLattice 2).Adj (![x, y] : Site 2) ![x + 1, y] := by
-- proof
  apply StatMech.Lattice.etp_adj_horiz x y

/--
[etp_horiz_wall_upperGap_blocked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeThickPointClose.lean)
-/
@[path]
private lemma etp_horiz_wall_upperGap_blocked_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {T : Set (Site 2)}
  {x y : ℤ}
-- given
  (hsat : ksc_KingSaturated Vc T)
  (hL : (![x - 1, y] : Site 2) ∈ T)
  (hR : (![x + 1, y] : Site 2) ∈ jil_offSupportInterior Vc)
  (hRnT : (![x + 1, y] : Site 2) ∉ T) :
-- imply
  (![x, y + 1] : Site 2) ∉ jil_offSupportInterior Vc := by
-- proof
  apply StatMech.Lattice.etp_horiz_wall_upperGap_blocked Vc hsat hL hR hRnT

/--
[etp_horiz_wall_lowerGap_blocked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeThickPointClose.lean)
-/
@[path]
private lemma etp_horiz_wall_lowerGap_blocked_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {T : Set (Site 2)}
  {x y : ℤ}
-- given
  (hsat : ksc_KingSaturated Vc T)
  (hL : (![x - 1, y] : Site 2) ∈ T)
  (hR : (![x + 1, y] : Site 2) ∈ jil_offSupportInterior Vc)
  (hRnT : (![x + 1, y] : Site 2) ∉ T) :
-- imply
  (![x, y - 1] : Site 2) ∉ jil_offSupportInterior Vc := by
-- proof
  apply StatMech.Lattice.etp_horiz_wall_lowerGap_blocked Vc hsat hL hR hRnT

/--
[etp_horiz_wall_gaps_blocked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeThickPointClose.lean)
-/
@[path]
private lemma etp_horiz_wall_gaps_blocked_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {T : Set (Site 2)}
  {x y : ℤ}
-- given
  (hsat : ksc_KingSaturated Vc T)
  (hTsub : T ⊆ jil_offSupportInterior Vc)
  (hL : (![x - 1, y] : Site 2) ∈ T)
  (hR : (![x + 1, y] : Site 2) ∈ jil_offSupportInterior Vc)
  (hRnT : (![x + 1, y] : Site 2) ∉ T) :
-- imply
  (![x, y] : Site 2) ∈ Vc.support ∧ (![x, y + 1] : Site 2) ∉ jil_offSupportInterior Vc ∧ (![x, y - 1] : Site 2) ∉ jil_offSupportInterior Vc := by
-- proof
  apply StatMech.Lattice.etp_horiz_wall_gaps_blocked Vc hsat hTsub hL hR hRnT

/--
[etp_thickPoint_of_swCorner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeThickPointClose.lean)
-/
@[path]
private lemma etp_thickPoint_of_swCorner_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {q : Site 2}
-- given
  (hW : (![q 0 - 1, q 1] : Site 2) ∈ Vc.support)
  (hS : (![q 0, q 1 - 1] : Site 2) ∈ Vc.support)
  (hC : (![q 0 - 1, q 1 - 1] : Site 2) ∈ Vc.support)
  (hnon : s((![q 0 - 1, q 1] : Site 2), (![q 0 - 1, q 1 - 1] : Site 2)) ∉ Vc.edges ∨ s((![q 0, q 1 - 1] : Site 2), (![q 0 - 1, q 1 - 1] : Site 2)) ∉ Vc.edges) :
-- imply
  kns_ThickPoint Vc := by
-- proof
  apply StatMech.Lattice.etp_thickPoint_of_swCorner Vc hW hS hC hnon

/--
[etp_swCorner_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeThickPointClose.lean)
-/
@[path]
private lemma etp_swCorner_dichotomy_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {T : Set (Site 2)}
  {q : Site 2}
  {M : ℤ}
-- given
  (hsat : ksc_KingSaturated Vc T)
  (hTsub : T ⊆ jil_offSupportInterior Vc)
  (hqI : q ∈ jil_offSupportInterior Vc)
  (hqnT : q ∉ T)
  (hmin : ∀ z ∈ jil_offSupportInterior Vc, z ∉ T → rlc_lexMeasure M q ≤ rlc_lexMeasure M z)
  (hqbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
  (hCbox : (-M < q 0 - 1 ∧ q 0 - 1 ≤ M) ∧ (-M < q 1 - 1 ∧ q 1 - 1 ≤ M)) :
-- imply
  (![q 0 - 1, q 1 - 1] : Site 2) ∈ Vc.support ∨ (![q 0 - 1, q 1 - 1] : Site 2) ∉ jil_offSupportInterior Vc := by
-- proof
  apply StatMech.Lattice.etp_swCorner_dichotomy Vc hsat hTsub hqI hqnT M hmin hqbox hCbox

/--
[etp_escape_structure_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeThickPointClose.lean)
-/
@[path]
private lemma etp_escape_structure_box_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hsep : kns_KingSeparation Vc seed) :
-- imply
  ∃ (T : Set (Site 2)), seed ∈ T ∧ T ⊆ jil_offSupportInterior Vc ∧ ksc_KingSaturated Vc T ∧ ∃ (M : ℤ) (q : Site 2), q ∈ jil_offSupportInterior Vc ∧ q ∉ T ∧ (∀ z ∈ jil_offSupportInterior Vc, z ∉ T → rlc_lexMeasure M q ≤ rlc_lexMeasure M z) ∧ (![q 0 - 1, q 1] : Site 2) ∈ Vc.support ∧ (![q 0, q 1 - 1] : Site 2) ∈ Vc.support ∧ ((-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M)) ∧ ((-M < q 0 - 1 ∧ q 0 - 1 ≤ M) ∧ (-M < q 1 - 1 ∧ q 1 - 1 ≤ M)) := by
-- proof
  apply StatMech.Lattice.etp_escape_structure_box Vc hsep

/--
[etp_noKingSeparation_of_fourThin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeThickPointClose.lean)
-/
@[path]
private lemma etp_noKingSeparation_of_fourThin_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseedI : seed ∈ jil_offSupportInterior Vc)
  (hthin : mci_FourThin Vc)
  (hres : etp_EscapeWallThick Vc seed) :
-- imply
  ksc_NoKingSeparation Vc seed := by
-- proof
  apply StatMech.Lattice.etp_noKingSeparation_of_fourThin Vc hseedI hthin hres

/--
[etp_kingRowLinked_of_fourThin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeThickPointClose.lean)
-/
@[path]
private lemma etp_kingRowLinked_of_fourThin_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseedI : seed ∈ jil_offSupportInterior Vc)
  (hthin : mci_FourThin Vc)
  (hres : etp_EscapeWallThick Vc seed) :
-- imply
  mci_KingRowLinked Vc seed := by
-- proof
  apply StatMech.Lattice.etp_kingRowLinked_of_fourThin Vc hseedI hthin hres

/--
[etp_kingInteriorConnected_of_fourThin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeThickPointClose.lean)
-/
@[path]
private lemma etp_kingInteriorConnected_of_fourThin_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z₀ : Site 2}
-- given
  (hz₀ : z₀ ∈ jil_offSupportInterior Vc)
  (hthin : mci_FourThin Vc)
  (hres : ∀ seed ∈ jil_offSupportInterior Vc, etp_EscapeWallThick Vc seed) :
-- imply
  mci_KingInteriorConnected Vc := by
-- proof
  apply StatMech.Lattice.etp_kingInteriorConnected_of_fourThin Vc hz₀ hthin hres

/--
[etp_escapeWallThick_of_escapeThickPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeThickPointClose.lean)
-/
@[path]
private lemma etp_escapeWallThick_of_escapeThickPoint_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hktp : kns_EscapeThickPoint Vc seed) :
-- imply
  etp_EscapeWallThick Vc seed := by
-- proof
  apply StatMech.Lattice.etp_escapeWallThick_of_escapeThickPoint Vc hktp

/--
[etp_fjord_escapeWallThick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeThickPointClose.lean)
-/
@[path]
private lemma etp_fjord_escapeWallThick_eq :
-- imply
  etp_EscapeWallThick sdc_fjord (![5, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.etp_fjord_escapeWallThick

/--
[etp_fjord_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeThickPointClose.lean)
-/
@[path]
private lemma etp_fjord_nonvacuous_eq :
-- imply
  kns_KingSeparation sdc_fjord (![5, 1] : Site 2) ∧ kns_ThickPoint sdc_fjord ∧ etp_EscapeWallThick sdc_fjord (![5, 1] : Site 2) ∧ ¬ mci_FourThin sdc_fjord := by
-- proof
  apply StatMech.Lattice.etp_fjord_nonvacuous

/--
[etp_ksd_escapeWallThick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeThickPointClose.lean)
-/
@[path]
private lemma etp_ksd_escapeWallThick_eq :
-- imply
  etp_EscapeWallThick ksd_stair (![1, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.etp_ksd_escapeWallThick

/--
[etp_kda_escapeWallThick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeThickPointClose.lean)
-/
@[path]
private lemma etp_kda_escapeWallThick_eq :
-- imply
  etp_EscapeWallThick kda_stairDR (![3, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.etp_kda_escapeWallThick

/--
[etp_kingRowLinked_summary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeThickPointClose.lean)
-/
@[path]
private lemma etp_kingRowLinked_summary_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseedI : seed ∈ jil_offSupportInterior Vc)
  (hthin : mci_FourThin Vc) :
-- imply
  etp_EscapeWallThick Vc seed → mci_KingRowLinked Vc seed := by
-- proof
  apply StatMech.Lattice.etp_kingRowLinked_summary Vc hseedI hthin


-- created on 2026-10-23
