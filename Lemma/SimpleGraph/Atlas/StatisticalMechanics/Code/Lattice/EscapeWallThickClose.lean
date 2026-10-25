import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.EscapeWallThickClose.Part2
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[ewt_escapeRow_notMem_of_run](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeWallThickClose.lean)
-/
@[path]
private lemma ewt_escapeRow_notMem_of_run_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {T : Set (Site 2)}
  {q : Site 2}
  {lo hi x₁ : ℤ}
-- given
  (hsat : ksc_KingSaturated Vc T)
  (hTsub : T ⊆ jil_offSupportInterior Vc)
  (hqnT : q ∉ T)
  (hloff : (![lo, q 1] : Site 2) ∉ Vc.support)
  (hlolo : lo ≤ q 0)
  (hqhi : q 0 ≤ hi)
  (hx₁lo : lo ≤ x₁)
  (hx₁hi : x₁ ≤ hi)
  (hrun : ∀ t : ℤ, lo ≤ t → t ≤ hi → (![t, q 1] : Site 2) ∉ Vc.support) :
-- imply
  (![x₁, q 1] : Site 2) ∉ T := by
-- proof
  apply StatMech.Lattice.ewt_escapeRow_notMem_of_run Vc hsat hTsub hqnT hloff hlolo hqhi hx₁lo hx₁hi hrun

/--
[ewt_escapeRow_down_onSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeWallThickClose.lean)
-/
@[path]
private lemma ewt_escapeRow_down_onSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {T : Set (Site 2)}
  {q : Site 2}
  {M : ℤ}
  {wx : ℤ}
-- given
  (hsat : ksc_KingSaturated Vc T)
  (hmin : ∀ z ∈ jil_offSupportInterior Vc, z ∉ T → rlc_lexMeasure M q ≤ rlc_lexMeasure M z)
  (hqbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
  (hw : (![wx, q 1] : Site 2) ∈ jil_offSupportInterior Vc)
  (hwnT : (![wx, q 1] : Site 2) ∉ T)
  (hwbox : (-M < wx ∧ wx ≤ M) ∧ (-M < q 1 - 1 ∧ q 1 - 1 ≤ M)) :
-- imply
  (![wx, q 1 - 1] : Site 2) ∈ Vc.support := by
-- proof
  apply StatMech.Lattice.ewt_escapeRow_down_onSupport Vc hsat M hmin hqbox hw hwnT hwbox

/--
[ewt_runBottom_onSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeWallThickClose.lean)
-/
@[path]
private lemma ewt_runBottom_onSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {T : Set (Site 2)}
  {q : Site 2}
  {M : ℤ}
  {lo hi : ℤ}
  {x : ℤ}
-- given
  (hsat : ksc_KingSaturated Vc T)
  (hTsub : T ⊆ jil_offSupportInterior Vc)
  (hqnT : q ∉ T)
  (hmin : ∀ z ∈ jil_offSupportInterior Vc, z ∉ T → rlc_lexMeasure M q ≤ rlc_lexMeasure M z)
  (hqbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
  (hq1box : -M < q 1 - 1 ∧ q 1 - 1 ≤ M)
  (hloff : (![lo, q 1] : Site 2) ∉ Vc.support)
  (hlolo : lo ≤ q 0)
  (hqhi : q 0 ≤ hi)
  (hrun : ∀ t : ℤ, lo ≤ t → t ≤ hi → (![t, q 1] : Site 2) ∉ Vc.support)
  (hrunI : ∀ t : ℤ, lo ≤ t → t ≤ hi → (![t, q 1] : Site 2) ∈ jil_offSupportInterior Vc)
  (hxlo : lo ≤ x)
  (hxhi : x ≤ hi)
  (hxbox : -M < x ∧ x ≤ M) :
-- imply
  (![x, q 1 - 1] : Site 2) ∈ Vc.support := by
-- proof
  apply StatMech.Lattice.ewt_runBottom_onSupport Vc hsat hTsub hqnT M hmin hqbox hq1box hloff hlolo hqhi hrun hrunI hxlo hxhi hxbox

/--
[ewt_vert_wall_rightGap_blocked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeWallThickClose.lean)
-/
@[path]
private lemma ewt_vert_wall_rightGap_blocked_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {T : Set (Site 2)}
  {x y : ℤ}
-- given
  (hsat : ksc_KingSaturated Vc T)
  (hD : (![x, y - 1] : Site 2) ∈ T)
  (hU : (![x, y + 1] : Site 2) ∈ jil_offSupportInterior Vc)
  (hUnT : (![x, y + 1] : Site 2) ∉ T) :
-- imply
  (![x + 1, y] : Site 2) ∉ jil_offSupportInterior Vc := by
-- proof
  apply StatMech.Lattice.ewt_vert_wall_rightGap_blocked Vc hsat hD hU hUnT

/--
[ewt_vert_wall_leftGap_blocked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeWallThickClose.lean)
-/
@[path]
private lemma ewt_vert_wall_leftGap_blocked_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {T : Set (Site 2)}
  {x y : ℤ}
-- given
  (hsat : ksc_KingSaturated Vc T)
  (hD : (![x, y - 1] : Site 2) ∈ T)
  (hU : (![x, y + 1] : Site 2) ∈ jil_offSupportInterior Vc)
  (hUnT : (![x, y + 1] : Site 2) ∉ T) :
-- imply
  (![x - 1, y] : Site 2) ∉ jil_offSupportInterior Vc := by
-- proof
  apply StatMech.Lattice.ewt_vert_wall_leftGap_blocked Vc hsat hD hU hUnT

/--
[ewt_vert_wall_gaps_blocked](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeWallThickClose.lean)
-/
@[path]
private lemma ewt_vert_wall_gaps_blocked_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {T : Set (Site 2)}
  {x y : ℤ}
-- given
  (hsat : ksc_KingSaturated Vc T)
  (hTsub : T ⊆ jil_offSupportInterior Vc)
  (hD : (![x, y - 1] : Site 2) ∈ T)
  (hU : (![x, y + 1] : Site 2) ∈ jil_offSupportInterior Vc)
  (hUnT : (![x, y + 1] : Site 2) ∉ T) :
-- imply
  (![x, y] : Site 2) ∈ Vc.support ∧ (![x + 1, y] : Site 2) ∉ jil_offSupportInterior Vc ∧ (![x - 1, y] : Site 2) ∉ jil_offSupportInterior Vc := by
-- proof
  apply StatMech.Lattice.ewt_vert_wall_gaps_blocked Vc hsat hTsub hD hU hUnT

/--
[ewt_escape_structure_rowbox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeWallThickClose.lean)
-/
@[path]
private lemma ewt_escape_structure_rowbox_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hsep : kns_KingSeparation Vc seed) :
-- imply
  ∃ (T : Set (Site 2)), seed ∈ T ∧ T ⊆ jil_offSupportInterior Vc ∧ ksc_KingSaturated Vc T ∧ ∃ (M : ℤ) (q : Site 2), q ∈ jil_offSupportInterior Vc ∧ q ∉ T ∧ (∀ z ∈ jil_offSupportInterior Vc, z ∉ T → rlc_lexMeasure M q ≤ rlc_lexMeasure M z) ∧ (![q 0 - 1, q 1] : Site 2) ∈ Vc.support ∧ (![q 0, q 1 - 1] : Site 2) ∈ Vc.support ∧ ((-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M)) ∧ (-M < q 1 - 1 ∧ q 1 - 1 ≤ M) ∧ (-M < q 0 - 1 ∧ q 0 - 1 ≤ M) := by
-- proof
  apply StatMech.Lattice.ewt_escape_structure_rowbox Vc hsep

/--
[ewt_noKingSeparation_of_fourThin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeWallThickClose.lean)
-/
@[path]
private lemma ewt_noKingSeparation_of_fourThin_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseedI : seed ∈ jil_offSupportInterior Vc)
  (hthin : mci_FourThin Vc)
  (hres : ewt_BottomWallThick Vc seed) :
-- imply
  ksc_NoKingSeparation Vc seed := by
-- proof
  apply StatMech.Lattice.ewt_noKingSeparation_of_fourThin Vc hseedI hthin hres

/--
[ewt_kingRowLinked_of_fourThin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeWallThickClose.lean)
-/
@[path]
private lemma ewt_kingRowLinked_of_fourThin_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseedI : seed ∈ jil_offSupportInterior Vc)
  (hthin : mci_FourThin Vc)
  (hres : ewt_BottomWallThick Vc seed) :
-- imply
  mci_KingRowLinked Vc seed := by
-- proof
  apply StatMech.Lattice.ewt_kingRowLinked_of_fourThin Vc hseedI hthin hres

/--
[ewt_bottomWallThick_of_escapeWallThick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeWallThickClose.lean)
-/
@[path]
private lemma ewt_bottomWallThick_of_escapeWallThick_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hetp : etp_EscapeWallThick Vc seed) :
-- imply
  ewt_BottomWallThick Vc seed := by
-- proof
  apply StatMech.Lattice.ewt_bottomWallThick_of_escapeWallThick Vc hetp

/--
[ewt_bottomWallThick_of_escapeThickPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeWallThickClose.lean)
-/
@[path]
private lemma ewt_bottomWallThick_of_escapeThickPoint_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hktp : kns_EscapeThickPoint Vc seed) :
-- imply
  ewt_BottomWallThick Vc seed := by
-- proof
  apply StatMech.Lattice.ewt_bottomWallThick_of_escapeThickPoint Vc hktp

/--
[ewt_fjord_bottomWallThick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeWallThickClose.lean)
-/
@[path]
private lemma ewt_fjord_bottomWallThick_eq :
-- imply
  ewt_BottomWallThick sdc_fjord (![5, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.ewt_fjord_bottomWallThick

/--
[ewt_fjord_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeWallThickClose.lean)
-/
@[path]
private lemma ewt_fjord_nonvacuous_eq :
-- imply
  kns_KingSeparation sdc_fjord (![5, 1] : Site 2) ∧ kns_ThickPoint sdc_fjord ∧ ewt_BottomWallThick sdc_fjord (![5, 1] : Site 2) ∧ ¬ mci_FourThin sdc_fjord := by
-- proof
  apply StatMech.Lattice.ewt_fjord_nonvacuous

/--
[ewt_ksd_bottomWallThick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeWallThickClose.lean)
-/
@[path]
private lemma ewt_ksd_bottomWallThick_eq :
-- imply
  ewt_BottomWallThick ksd_stair (![1, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.ewt_ksd_bottomWallThick

/--
[ewt_kda_bottomWallThick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeWallThickClose.lean)
-/
@[path]
private lemma ewt_kda_bottomWallThick_eq :
-- imply
  ewt_BottomWallThick kda_stairDR (![3, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.ewt_kda_bottomWallThick

/--
[ewt_kingRowLinked_summary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EscapeWallThickClose.lean)
-/
@[path]
private lemma ewt_kingRowLinked_summary_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseedI : seed ∈ jil_offSupportInterior Vc)
  (hthin : mci_FourThin Vc) :
-- imply
  ewt_BottomWallThick Vc seed → mci_KingRowLinked Vc seed := by
-- proof
  apply StatMech.Lattice.ewt_kingRowLinked_summary Vc hseedI hthin


-- created on 2026-10-23
