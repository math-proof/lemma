import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Lattice.KingNoSeparationClose.Part3
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[kns_fourThin_noKingSeparation_examples](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingNoSeparationClose.lean)
-/
@[path]
private lemma kns_fourThin_noKingSeparation_examples_eq :
-- imply
  (mci_FourThin ksd_stair ∧ ksc_NoKingSeparation ksd_stair (![1, 1] : Site 2)) ∧ (mci_FourThin kda_stairDR ∧ ksc_NoKingSeparation kda_stairDR (![3, 1] : Site 2)) := by
-- proof
  apply StatMech.Lattice.kns_fourThin_noKingSeparation_examples

/--
[kns_fjord_not_fourThin_has_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingNoSeparationClose.lean)
-/
@[path]
private lemma kns_fjord_not_fourThin_has_separation_eq :
-- imply
  ¬ mci_FourThin sdc_fjord ∧ ¬ ksc_NoKingSeparation sdc_fjord (![5, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.kns_fjord_not_fourThin_has_separation

/--
[kns_offSupport_neighbor_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingNoSeparationClose.lean)
-/
@[path]
private lemma kns_offSupport_neighbor_interior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z w : Site 2}
-- given
  (hz : z ∈ jil_offSupportInterior Vc)
  (hadj : (hypercubicLattice 2).Adj z w)
  (hwoff : w ∉ Vc.support) :
-- imply
  w ∈ jil_offSupportInterior Vc := by
-- proof
  apply StatMech.Lattice.kns_offSupport_neighbor_interior Vc hz hadj hwoff

/--
[kns_lexBelow_axial_onSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingNoSeparationClose.lean)
-/
@[path]
private lemma kns_lexBelow_axial_onSupport_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {T : Set (Site 2)}
  {q : Site 2}
  {M : ℤ}
  {w : Site 2}
-- given
  (hsat : ksc_KingSaturated Vc T)
  (hTsub : T ⊆ jil_offSupportInterior Vc)
  (hqI : q ∈ jil_offSupportInterior Vc)
  (hqnT : q ∉ T)
  (hmin : ∀ z ∈ jil_offSupportInterior Vc, z ∉ T → rlc_lexMeasure M q ≤ rlc_lexMeasure M z)
  (hqbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
  (hwadj : (hypercubicLattice 2).Adj q w)
  (hwbox : (-M < w 0 ∧ w 0 ≤ M) ∧ (-M < w 1 ∧ w 1 ≤ M))
  (hlex : w 1 < q 1 ∨ (w 1 = q 1 ∧ w 0 < q 0)) :
-- imply
  w ∈ Vc.support := by
-- proof
  apply StatMech.Lattice.kns_lexBelow_axial_onSupport Vc hsat hTsub hqI hqnT M hmin hqbox hwadj hwbox hlex

/--
[kns_escape_axials_onSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingNoSeparationClose.lean)
-/
@[path]
private lemma kns_escape_axials_onSupport_eq
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
  (hWbox : (-M < q 0 - 1 ∧ q 0 - 1 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
  (hSbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 - 1 ∧ q 1 - 1 ≤ M)) :
-- imply
  (![q 0 - 1, q 1] : Site 2) ∈ Vc.support ∧ (![q 0, q 1 - 1] : Site 2) ∈ Vc.support := by
-- proof
  apply StatMech.Lattice.kns_escape_axials_onSupport Vc hsat hTsub hqI hqnT M hmin hqbox hWbox hSbox

/--
[kns_lexBelow_diag_corner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingNoSeparationClose.lean)
-/
@[path]
private lemma kns_lexBelow_diag_corner_eq
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
  apply StatMech.Lattice.kns_lexBelow_diag_corner Vc hsat hTsub hqI hqnT M hmin hqbox hCbox

/--
[kns_lexBelow_diag_corner_SE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingNoSeparationClose.lean)
-/
@[path]
private lemma kns_lexBelow_diag_corner_SE_eq
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
  (hCbox : (-M < q 0 + 1 ∧ q 0 + 1 ≤ M) ∧ (-M < q 1 - 1 ∧ q 1 - 1 ≤ M)) :
-- imply
  (![q 0 + 1, q 1 - 1] : Site 2) ∈ Vc.support ∨ (![q 0 + 1, q 1 - 1] : Site 2) ∉ jil_offSupportInterior Vc := by
-- proof
  apply StatMech.Lattice.kns_lexBelow_diag_corner_SE Vc hsat hTsub hqI hqnT M hmin hqbox hCbox

/--
[kns_right_mem_interior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingNoSeparationClose.lean)
-/
@[path]
private lemma kns_right_mem_interior_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {x y : ℤ}
-- given
  (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
  (hright : (![x + 1, y] : Site 2) ∉ Vc.support) :
-- imply
  (![x + 1, y] : Site 2) ∈ jil_offSupportInterior Vc := by
-- proof
  apply StatMech.Lattice.kns_right_mem_interior Vc hz hright

/--
[kns_row_complete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingNoSeparationClose.lean)
-/
@[path]
private lemma kns_row_complete_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {T : Set (Site 2)}
  {lo hi y x₀ x₁ : ℤ}
-- given
  (hsat : ksc_KingSaturated Vc T)
  (hTsub : T ⊆ jil_offSupportInterior Vc)
  (hx₀T : (![x₀, y] : Site 2) ∈ T)
  (hloff : (![lo, y] : Site 2) ∉ Vc.support)
  (hx₀lo : lo ≤ x₀)
  (hx₀hi : x₀ ≤ hi)
  (hx₁lo : lo ≤ x₁)
  (hx₁hi : x₁ ≤ hi)
  (hrun : ∀ t : ℤ, lo ≤ t → t ≤ hi → (![t, y] : Site 2) ∉ Vc.support) :
-- imply
  (![x₁, y] : Site 2) ∈ T := by
-- proof
  apply StatMech.Lattice.kns_row_complete Vc hsat hTsub hx₀T hloff hx₀lo hx₀hi hx₁lo hx₁hi hrun

/--
[kns_kingSeparation_iff_not_noKingSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingNoSeparationClose.lean)
-/
@[path]
private lemma kns_kingSeparation_iff_not_noKingSeparation_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (_hseedI : seed ∈ jil_offSupportInterior Vc) :
-- imply
  kns_KingSeparation Vc seed ↔ ¬ ksc_NoKingSeparation Vc seed := by
-- proof
  apply StatMech.Lattice.kns_kingSeparation_iff_not_noKingSeparation Vc _hseedI

/--
[kns_thickPoint_iff_not_fourThin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingNoSeparationClose.lean)
-/
@[path]
private lemma kns_thickPoint_iff_not_fourThin_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a} :
-- imply
  kns_ThickPoint Vc ↔ ¬ mci_FourThin Vc := by
-- proof
  apply StatMech.Lattice.kns_thickPoint_iff_not_fourThin Vc

/--
[kns_exists_lexMin_escape](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingNoSeparationClose.lean)
-/
@[path]
private lemma kns_exists_lexMin_escape_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {T : Set (Site 2)}
  {z : Site 2}
  {M : ℤ}
-- given
  (hzI : z ∈ jil_offSupportInterior Vc)
  (hznT : z ∉ T) :
-- imply
  ∃ q ∈ jil_offSupportInterior Vc, q ∉ T ∧ ∀ w ∈ jil_offSupportInterior Vc, w ∉ T → rlc_lexMeasure M q ≤ rlc_lexMeasure M w := by
-- proof
  apply StatMech.Lattice.kns_exists_lexMin_escape Vc hzI hznT M

/--
[kns_kingSeparation_escape_structure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingNoSeparationClose.lean)
-/
@[path]
private lemma kns_kingSeparation_escape_structure_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hsep : kns_KingSeparation Vc seed) :
-- imply
  ∃ (T : Set (Site 2)), seed ∈ T ∧ T ⊆ jil_offSupportInterior Vc ∧ ksc_KingSaturated Vc T ∧ ∃ (M : ℤ) (q : Site 2), q ∈ jil_offSupportInterior Vc ∧ q ∉ T ∧ (∀ z ∈ jil_offSupportInterior Vc, z ∉ T → rlc_lexMeasure M q ≤ rlc_lexMeasure M z) ∧ (![q 0 - 1, q 1] : Site 2) ∈ Vc.support ∧ (![q 0, q 1 - 1] : Site 2) ∈ Vc.support := by
-- proof
  apply StatMech.Lattice.kns_kingSeparation_escape_structure Vc hsep

/--
[kns_noKingSeparation_of_fourThin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingNoSeparationClose.lean)
-/
@[path]
private lemma kns_noKingSeparation_of_fourThin_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseedI : seed ∈ jil_offSupportInterior Vc)
  (hthin : mci_FourThin Vc)
  (hres : kns_EscapeThickPoint Vc seed) :
-- imply
  ksc_NoKingSeparation Vc seed := by
-- proof
  apply StatMech.Lattice.kns_noKingSeparation_of_fourThin Vc hseedI hthin hres

/--
[kns_escapeThickPoint_of_noKingSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingNoSeparationClose.lean)
-/
@[path]
private lemma kns_escapeThickPoint_of_noKingSeparation_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hns : ksc_NoKingSeparation Vc seed) :
-- imply
  kns_EscapeThickPoint Vc seed := by
-- proof
  apply StatMech.Lattice.kns_escapeThickPoint_of_noKingSeparation Vc hns

/--
[kns_kingRowLinked_of_fourThin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingNoSeparationClose.lean)
-/
@[path]
private lemma kns_kingRowLinked_of_fourThin_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseedI : seed ∈ jil_offSupportInterior Vc)
  (hthin : mci_FourThin Vc)
  (hres : kns_EscapeThickPoint Vc seed) :
-- imply
  mci_KingRowLinked Vc seed := by
-- proof
  apply StatMech.Lattice.kns_kingRowLinked_of_fourThin Vc hseedI hthin hres

/--
[kns_kingInteriorConnected_of_fourThin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingNoSeparationClose.lean)
-/
@[path]
private lemma kns_kingInteriorConnected_of_fourThin_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z₀ : Site 2}
-- given
  (hz₀ : z₀ ∈ jil_offSupportInterior Vc)
  (hthin : mci_FourThin Vc)
  (hres : ∀ seed ∈ jil_offSupportInterior Vc, kns_EscapeThickPoint Vc seed) :
-- imply
  mci_KingInteriorConnected Vc := by
-- proof
  apply StatMech.Lattice.kns_kingInteriorConnected_of_fourThin Vc hz₀ hthin hres

/--
[kns_fjord_thickPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingNoSeparationClose.lean)
-/
@[path]
private lemma kns_fjord_thickPoint_eq :
-- imply
  kns_ThickPoint sdc_fjord := by
-- proof
  apply StatMech.Lattice.kns_fjord_thickPoint

/--
[kns_fjord_kingSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingNoSeparationClose.lean)
-/
@[path]
private lemma kns_fjord_kingSeparation_eq :
-- imply
  kns_KingSeparation sdc_fjord (![5, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.kns_fjord_kingSeparation

/--
[kns_fjord_escapeThickPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingNoSeparationClose.lean)
-/
@[path]
private lemma kns_fjord_escapeThickPoint_eq :
-- imply
  kns_EscapeThickPoint sdc_fjord (![5, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.kns_fjord_escapeThickPoint

/--
[kns_fjord_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingNoSeparationClose.lean)
-/
@[path]
private lemma kns_fjord_nonvacuous_eq :
-- imply
  kns_KingSeparation sdc_fjord (![5, 1] : Site 2) ∧ kns_ThickPoint sdc_fjord ∧ kns_EscapeThickPoint sdc_fjord (![5, 1] : Site 2) ∧ ¬ mci_FourThin sdc_fjord := by
-- proof
  apply StatMech.Lattice.kns_fjord_nonvacuous

/--
[kns_ksd_escapeThickPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingNoSeparationClose.lean)
-/
@[path]
private lemma kns_ksd_escapeThickPoint_eq :
-- imply
  kns_EscapeThickPoint ksd_stair (![1, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.kns_ksd_escapeThickPoint

/--
[kns_kda_escapeThickPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/KingNoSeparationClose.lean)
-/
@[path]
private lemma kns_kda_escapeThickPoint_eq :
-- imply
  kns_EscapeThickPoint kda_stairDR (![3, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.kns_kda_escapeThickPoint


-- created on 2026-10-23
