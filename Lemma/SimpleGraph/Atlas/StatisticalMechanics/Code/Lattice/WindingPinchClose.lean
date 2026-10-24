import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.WindingPinchClose
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[wpc_fig8_raycount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingPinchClose.lean)
-/
@[path]
private lemma wpc_fig8_raycount_eq
  {z : Site 2} :
-- imply
  jec_rayCount z wpc_fig8 = (if 0 ≤ z 0 - 1 ∧ 0 ≤ z 1 - 1 ∧ z 1 - 1 ≤ 0 + (2:ℤ) - 1 then 1 else 0) + (if 2 ≤ z 0 - 1 ∧ 0 ≤ z 1 - 1 ∧ z 1 - 1 ≤ 0 + (2:ℤ) - 1 then 1 else 0) + (if 4 ≤ z 0 - 1 ∧ 2 ≤ z 1 - 1 ∧ z 1 - 1 ≤ 2 + (2:ℤ) - 1 then 1 else 0) + (if 2 ≤ z 0 - 1 ∧ 2 ≤ z 1 - 1 ∧ z 1 - 1 ≤ 2 + (2:ℤ) - 1 then 1 else 0) := by
-- proof
  apply StatMech.Lattice.wpc_fig8_raycount z

/--
[wpc_fig8_support_locus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingPinchClose.lean)
-/
@[path]
private lemma wpc_fig8_support_locus_eq
  {p : Site 2}
-- given
  (hp : p ∈ wpc_fig8.support) :
-- imply
  (p 1 = 2 ∧ 0 ≤ p 0 ∧ p 0 ≤ 2) ∨ (p 0 = 0 ∧ 0 ≤ p 1 ∧ p 1 ≤ 2) ∨ (p 1 = 0 ∧ 0 ≤ p 0 ∧ p 0 ≤ 2) ∨ (p 0 = 2 ∧ 0 ≤ p 1 ∧ p 1 ≤ 2) ∨ (p 1 = 2 ∧ 2 ≤ p 0 ∧ p 0 ≤ 4) ∨ (p 0 = 4 ∧ 2 ≤ p 1 ∧ p 1 ≤ 4) ∨ (p 1 = 4 ∧ 2 ≤ p 0 ∧ p 0 ≤ 4) ∨ (p 0 = 2 ∧ 2 ≤ p 1 ∧ p 1 ≤ 4) := by
-- proof
  apply StatMech.Lattice.wpc_fig8_support_locus p hp

/--
[wpc_fig8_off_11](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingPinchClose.lean)
-/
@[path]
private lemma wpc_fig8_off_11_eq :
-- imply
  (![1, 1] : Site 2) ∉ wpc_fig8.support := by
-- proof
  apply StatMech.Lattice.wpc_fig8_off_11

/--
[wpc_fig8_off_33](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingPinchClose.lean)
-/
@[path]
private lemma wpc_fig8_off_33_eq :
-- imply
  (![3, 3] : Site 2) ∉ wpc_fig8.support := by
-- proof
  apply StatMech.Lattice.wpc_fig8_off_33

/--
[wpc_fig8_interior_11](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingPinchClose.lean)
-/
@[path]
private lemma wpc_fig8_interior_11_eq :
-- imply
  (![1, 1] : Site 2) ∈ jec_leftRegion wpc_fig8 := by
-- proof
  apply StatMech.Lattice.wpc_fig8_interior_11

/--
[wpc_fig8_interior_33](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingPinchClose.lean)
-/
@[path]
private lemma wpc_fig8_interior_33_eq :
-- imply
  (![3, 3] : Site 2) ∈ jec_leftRegion wpc_fig8 := by
-- proof
  apply StatMech.Lattice.wpc_fig8_interior_33

/--
[wpc_fig8_mem_interior_11](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingPinchClose.lean)
-/
@[path]
private lemma wpc_fig8_mem_interior_11_eq :
-- imply
  (![1, 1] : Site 2) ∈ jil_offSupportInterior wpc_fig8 := by
-- proof
  apply StatMech.Lattice.wpc_fig8_mem_interior_11

/--
[wpc_fig8_mem_interior_33](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingPinchClose.lean)
-/
@[path]
private lemma wpc_fig8_mem_interior_33_eq :
-- imply
  (![3, 3] : Site 2) ∈ jil_offSupportInterior wpc_fig8 := by
-- proof
  apply StatMech.Lattice.wpc_fig8_mem_interior_33

/--
[wpc_support_cells](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingPinchClose.lean)
-/
@[path]
private lemma wpc_support_cells_eq
  {p : Site 2}
-- given
  (hp : p ∈ wpc_fig8.support) :
-- imply
  p = (![0,0]:Site 2) ∨ p = (![1,0]:Site 2) ∨ p = (![2,0]:Site 2) ∨ p = (![0,1]:Site 2) ∨ p = (![2,1]:Site 2) ∨ p = (![0,2]:Site 2) ∨ p = (![1,2]:Site 2) ∨ p = (![2,2]:Site 2) ∨ p = (![3,2]:Site 2) ∨ p = (![4,2]:Site 2) ∨ p = (![2,3]:Site 2) ∨ p = (![4,3]:Site 2) ∨ p = (![2,4]:Site 2) ∨ p = (![3,4]:Site 2) ∨ p = (![4,4]:Site 2) := by
-- proof
  apply StatMech.Lattice.wpc_support_cells p hp

/--
[wpc_edges_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingPinchClose.lean)
-/
@[path]
private lemma wpc_edges_mem_eq :
-- imply
  ∀ e : Sym2 (Site 2), (e = s((![0,2]:Site 2),(![1,2]:Site 2)) ∨ e = s((![1,2]:Site 2),(![2,2]:Site 2)) ∨ e = s((![0,0]:Site 2),(![0,1]:Site 2)) ∨ e = s((![0,1]:Site 2),(![0,2]:Site 2)) ∨ e = s((![0,0]:Site 2),(![1,0]:Site 2)) ∨ e = s((![1,0]:Site 2),(![2,0]:Site 2)) ∨ e = s((![2,0]:Site 2),(![2,1]:Site 2)) ∨ e = s((![2,1]:Site 2),(![2,2]:Site 2)) ∨ e = s((![2,2]:Site 2),(![3,2]:Site 2)) ∨ e = s((![3,2]:Site 2),(![4,2]:Site 2)) ∨ e = s((![4,2]:Site 2),(![4,3]:Site 2)) ∨ e = s((![4,3]:Site 2),(![4,4]:Site 2)) ∨ e = s((![2,4]:Site 2),(![3,4]:Site 2)) ∨ e = s((![3,4]:Site 2),(![4,4]:Site 2)) ∨ e = s((![2,2]:Site 2),(![2,3]:Site 2)) ∨ e = s((![2,3]:Site 2),(![2,4]:Site 2))) → e ∈ wpc_fig8.edges := by
-- proof
  apply StatMech.Lattice.wpc_edges_mem

/--
[wpc_fig8_fourThin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingPinchClose.lean)
-/
@[path]
private lemma wpc_fig8_fourThin_eq :
-- imply
  mci_FourThin wpc_fig8 := by
-- proof
  apply StatMech.Lattice.wpc_fig8_fourThin

/--
[wpc_on_Arow0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingPinchClose.lean)
-/
@[path]
private lemma wpc_on_Arow0_eq
  {c : ℤ}
-- given
  (h0 : 0 ≤ c)
  (h1 : c ≤ 2) :
-- imply
  (![c, 0] : Site 2) ∈ wpc_fig8.support := by
-- proof
  apply StatMech.Lattice.wpc_on_Arow0 c h0 h1

/--
[wpc_on_Arow2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingPinchClose.lean)
-/
@[path]
private lemma wpc_on_Arow2_eq
  {c : ℤ}
-- given
  (h0 : 0 ≤ c)
  (h1 : c ≤ 2) :
-- imply
  (![c, 2] : Site 2) ∈ wpc_fig8.support := by
-- proof
  apply StatMech.Lattice.wpc_on_Arow2 c h0 h1

/--
[wpc_on_Acol0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingPinchClose.lean)
-/
@[path]
private lemma wpc_on_Acol0_eq
  {r : ℤ}
-- given
  (h0 : 0 ≤ r)
  (h1 : r ≤ 2) :
-- imply
  (![0, r] : Site 2) ∈ wpc_fig8.support := by
-- proof
  apply StatMech.Lattice.wpc_on_Acol0 r h0 h1

/--
[wpc_on_Acol2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingPinchClose.lean)
-/
@[path]
private lemma wpc_on_Acol2_eq
  {r : ℤ}
-- given
  (h0 : 0 ≤ r)
  (h1 : r ≤ 2) :
-- imply
  (![2, r] : Site 2) ∈ wpc_fig8.support := by
-- proof
  apply StatMech.Lattice.wpc_on_Acol2 r h0 h1

/--
[wpc_fig8_singleton_saturated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingPinchClose.lean)
-/
@[path]
private lemma wpc_fig8_singleton_saturated_eq :
-- imply
  ksc_KingSaturated wpc_fig8 {(![1, 1] : Site 2)} := by
-- proof
  apply StatMech.Lattice.wpc_fig8_singleton_saturated

/--
[wpc_not_noKingSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingPinchClose.lean)
-/
@[path]
private lemma wpc_not_noKingSeparation_eq :
-- imply
  ¬ ksc_NoKingSeparation wpc_fig8 (![1, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.wpc_not_noKingSeparation

/--
[wpc_cat_crossArcThick_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingPinchClose.lean)
-/
@[path]
private lemma wpc_cat_crossArcThick_false_eq :
-- imply
  ¬ cat_CrossArcThick wpc_fig8 (![1, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.wpc_cat_crossArcThick_false

/--
[wpc_fig8_refutation_package](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WindingPinchClose.lean)
-/
@[path]
private lemma wpc_fig8_refutation_package_eq :
-- imply
  mci_FourThin wpc_fig8 ∧ (![1, 1] : Site 2) ∈ jil_offSupportInterior wpc_fig8 ∧ (![3, 3] : Site 2) ∈ jil_offSupportInterior wpc_fig8 ∧ ¬ ksc_NoKingSeparation wpc_fig8 (![1, 1] : Site 2) ∧ ¬ cat_CrossArcThick wpc_fig8 (![1, 1] : Site 2) := by
-- proof
  apply StatMech.Lattice.wpc_fig8_refutation_package


-- created on 2026-10-23
