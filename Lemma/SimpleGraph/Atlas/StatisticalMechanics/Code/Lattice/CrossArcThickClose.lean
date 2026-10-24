import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.CrossArcThickClose
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[cat_thickPoint_of_seCorner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossArcThickClose.lean)
-/
@[path]
private lemma cat_thickPoint_of_seCorner_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {e y : ℤ}
-- given
  (hE : (![e, y] : Site 2) ∈ Vc.support)
  (hB : (![e - 1, y - 1] : Site 2) ∈ Vc.support)
  (hC : (![e, y - 1] : Site 2) ∈ Vc.support)
  (hnon : s((![e, y] : Site 2), (![e, y - 1] : Site 2)) ∉ Vc.edges ∨ s((![e - 1, y - 1] : Site 2), (![e, y - 1] : Site 2)) ∉ Vc.edges) :
-- imply
  kns_ThickPoint Vc := by
-- proof
  apply StatMech.Lattice.cat_thickPoint_of_seCorner Vc hE hB hC hnon

/--
[cat_seCorner_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossArcThickClose.lean)
-/
@[path]
private lemma cat_seCorner_dichotomy_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {T : Set (Site 2)}
  {q : Site 2}
  {M e : ℤ}
-- given
  (hsat : ksc_KingSaturated Vc T)
  (hmin : ∀ z ∈ jil_offSupportInterior Vc, z ∉ T → rlc_lexMeasure M q ≤ rlc_lexMeasure M z)
  (hqbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
  (hCbox : (-M < e ∧ e ≤ M) ∧ (-M < q 1 - 1 ∧ q 1 - 1 ≤ M))
  (hwI : (![e - 1, q 1] : Site 2) ∈ jil_offSupportInterior Vc)
  (hwnT : (![e - 1, q 1] : Site 2) ∉ T) :
-- imply
  (![e, q 1 - 1] : Site 2) ∈ Vc.support ∨ (![e, q 1 - 1] : Site 2) ∉ jil_offSupportInterior Vc := by
-- proof
  apply StatMech.Lattice.cat_seCorner_dichotomy Vc hsat M e hmin hqbox hCbox hwI hwnT

/--
[cat_runEnd_corner_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossArcThickClose.lean)
-/
@[path]
private lemma cat_runEnd_corner_data_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {T : Set (Site 2)}
  {q : Site 2}
  {M : ℤ}
  {e : ℤ}
-- given
  (hsat : ksc_KingSaturated Vc T)
  (hTsub : T ⊆ jil_offSupportInterior Vc)
  (hqnT : q ∉ T)
  (hmin : ∀ z ∈ jil_offSupportInterior Vc, z ∉ T → rlc_lexMeasure M q ≤ rlc_lexMeasure M z)
  (hqbox : (-M < q 0 ∧ q 0 ≤ M) ∧ (-M < q 1 ∧ q 1 ≤ M))
  (hq1box : -M < q 1 - 1 ∧ q 1 - 1 ≤ M)
  (he₁ : q 0 < e)
  (heM : -M < e - 1 ∧ e - 1 ≤ M)
  (he₃ : ∀ x : ℤ, q 0 ≤ x → x < e → (![x, q 1] : Site 2) ∈ jil_offSupportInterior Vc) :
-- imply
  (![e - 1, q 1] : Site 2) ∈ jil_offSupportInterior Vc ∧ (![e - 1, q 1] : Site 2) ∉ T ∧ (![e - 1, q 1 - 1] : Site 2) ∈ Vc.support := by
-- proof
  apply StatMech.Lattice.cat_runEnd_corner_data Vc hsat hTsub M hqnT hmin hqbox hq1box he₁ heM he₃

/--
[cat_escape_structure_eastbox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossArcThickClose.lean)
-/
@[path]
private lemma cat_escape_structure_eastbox_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hsep : kns_KingSeparation Vc seed) :
-- imply
  ∃ (T : Set (Site 2)), seed ∈ T ∧ T ⊆ jil_offSupportInterior Vc ∧ ksc_KingSaturated Vc T ∧ ∃ (M₀ : ℤ) (q : Site 2), q ∈ jil_offSupportInterior Vc ∧ q ∉ T ∧ (∀ z ∈ jil_offSupportInterior Vc, z ∉ T → rlc_lexMeasure (M₀ + 1) q ≤ rlc_lexMeasure (M₀ + 1) z) ∧ (![q 0 - 1, q 1] : Site 2) ∈ Vc.support ∧ (![q 0, q 1 - 1] : Site 2) ∈ Vc.support ∧ ((-(M₀ + 1) < q 0 ∧ q 0 ≤ M₀ + 1) ∧ (-(M₀ + 1) < q 1 ∧ q 1 ≤ M₀ + 1)) ∧ (-(M₀ + 1) < q 1 - 1 ∧ q 1 - 1 ≤ M₀ + 1) ∧ (-(M₀ + 1) < q 0 - 1 ∧ q 0 - 1 ≤ M₀ + 1) ∧ (∀ z ∈ jec_leftRegion Vc, (-M₀ < z 0 ∧ z 0 ≤ M₀) ∧ (-M₀ < z 1 ∧ z 1 ≤ M₀)) := by
-- proof
  apply StatMech.Lattice.cat_escape_structure_eastbox Vc hsep

/--
[cat_noKingSeparation_of_fourThin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossArcThickClose.lean)
-/
@[path]
private lemma cat_noKingSeparation_of_fourThin_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseedI : seed ∈ jil_offSupportInterior Vc)
  (hthin : mci_FourThin Vc)
  (hres : cat_CrossArcThick Vc seed) :
-- imply
  ksc_NoKingSeparation Vc seed := by
-- proof
  apply StatMech.Lattice.cat_noKingSeparation_of_fourThin Vc hseedI hthin hres

/--
[cat_kingRowLinked_of_fourThin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossArcThickClose.lean)
-/
@[path]
private lemma cat_kingRowLinked_of_fourThin_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseedI : seed ∈ jil_offSupportInterior Vc)
  (hthin : mci_FourThin Vc)
  (hres : cat_CrossArcThick Vc seed) :
-- imply
  mci_KingRowLinked Vc seed := by
-- proof
  apply StatMech.Lattice.cat_kingRowLinked_of_fourThin Vc hseedI hthin hres

/--
[cat_kingInteriorConnected_of_fourThin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossArcThickClose.lean)
-/
@[path]
private lemma cat_kingInteriorConnected_of_fourThin_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z₀ : Site 2}
-- given
  (hz₀ : z₀ ∈ jil_offSupportInterior Vc)
  (hthin : mci_FourThin Vc)
  (hres : ∀ seed ∈ jil_offSupportInterior Vc, cat_CrossArcThick Vc seed) :
-- imply
  mci_KingInteriorConnected Vc := by
-- proof
  apply StatMech.Lattice.cat_kingInteriorConnected_of_fourThin Vc hz₀ hthin hres

/--
[cat_crossArcThick_of_runEndReconnect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossArcThickClose.lean)
-/
@[path]
private lemma cat_crossArcThick_of_runEndReconnect_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hgtp : gtp_RunEndReconnect Vc seed) :
-- imply
  cat_CrossArcThick Vc seed := by
-- proof
  apply StatMech.Lattice.cat_crossArcThick_of_runEndReconnect Vc hgtp

/--
[cat_crossArcThick_of_escapeWallThick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossArcThickClose.lean)
-/
@[path]
private lemma cat_crossArcThick_of_escapeWallThick_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hetp : etp_EscapeWallThick Vc seed) :
-- imply
  cat_CrossArcThick Vc seed := by
-- proof
  apply StatMech.Lattice.cat_crossArcThick_of_escapeWallThick Vc hetp

/--
[cat_fjord_crossArcThick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossArcThickClose.lean)
-/
@[path]
private lemma cat_fjord_crossArcThick_eq :
-- imply
  cat_CrossArcThick sdc_fjord (![5, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.cat_fjord_crossArcThick

/--
[cat_fjord_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossArcThickClose.lean)
-/
@[path]
private lemma cat_fjord_nonvacuous_eq :
-- imply
  kns_KingSeparation sdc_fjord (![5, 1] : Site 2) ∧ kns_ThickPoint sdc_fjord ∧ cat_CrossArcThick sdc_fjord (![5, 1] : Site 2) ∧ ¬ mci_FourThin sdc_fjord := by
-- proof
  apply StatMech.Lattice.cat_fjord_nonvacuous

/--
[cat_ksd_crossArcThick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossArcThickClose.lean)
-/
@[path]
private lemma cat_ksd_crossArcThick_eq :
-- imply
  cat_CrossArcThick ksd_stair (![1, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.cat_ksd_crossArcThick

/--
[cat_kda_crossArcThick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossArcThickClose.lean)
-/
@[path]
private lemma cat_kda_crossArcThick_eq :
-- imply
  cat_CrossArcThick kda_stairDR (![3, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.cat_kda_crossArcThick

/--
[cat_kingRowLinked_summary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CrossArcThickClose.lean)
-/
@[path]
private lemma cat_kingRowLinked_summary_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {seed : Site 2}
-- given
  (hseedI : seed ∈ jil_offSupportInterior Vc)
  (hthin : mci_FourThin Vc) :
-- imply
  cat_CrossArcThick Vc seed → mci_KingRowLinked Vc seed := by
-- proof
  apply StatMech.Lattice.cat_kingRowLinked_summary Vc hseedI hthin


-- created on 2026-10-23
