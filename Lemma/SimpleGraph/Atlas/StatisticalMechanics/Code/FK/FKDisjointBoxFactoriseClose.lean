import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.FKDisjointBoxFactoriseClose
open MeasureTheory Filter Topology Set StatMech.ConfigSpace StatMech.Lattice StatMech StatMech.FK


/--
[fdf_exists_common_cross_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDisjointBoxFactoriseClose.lean)
-/
@[path]
private lemma fdf_exists_common_cross_box_eq
  {d : ℕ}
  {P : Finset (Finset (Sym2 (Site d)))}
  {g : Multiplicative (Site d)} :
-- imply
  ∃ M : ℕ, ∀ T ∈ P, ∀ T' ∈ P, ∃ t : Finset (Sym2 (boxVerts d M)), T ∪ T'.image (fun e => g⁻¹ • e) = t.image (edgeIncl d M) := by
-- proof
  apply StatMech.FK.fdf_exists_common_cross_box P g

/--
[fdf_factorise_of_finiteBoxDisjointProductDom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDisjointBoxFactoriseClose.lean)
-/
@[path]
private lemma fdf_factorise_of_finiteBoxDisjointProductDom_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hfin : ftb_FiniteBoxDisjointProductDom hp hp1 (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))))) :
-- imply
  fwm_WiredDisjointBoxFactorise hp hp1 (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))) := by
-- proof
  apply StatMech.FK.fdf_factorise_of_finiteBoxDisjointProductDom hp hp1 hfin

/--
[fdf_factorise_of_boxCap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDisjointBoxFactoriseClose.lean)
-/
@[path]
private lemma fdf_factorise_of_boxCap_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hcap : fdb_BoxConditionalProductCap (d := d) hp hp1) :
-- imply
  fwm_WiredDisjointBoxFactorise hp hp1 (fun m => (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d))))) := by
-- proof
  apply StatMech.FK.fdf_factorise_of_boxCap hp hp1 hcap

/--
[fdf_wiredIV_isErgodic_of_boxCap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKDisjointBoxFactoriseClose.lean)
-/
@[path]
private lemma fdf_wiredIV_isErgodic_of_boxCap_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hcap : fdb_BoxConditionalProductCap (d := d) hp hp1) :
-- imply
  IsErgodic (G := Multiplicative (Site d)) (wiredInfiniteVolume d hp hp1 (by norm_num : (0 : ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))) := by
-- proof
  apply StatMech.FK.fdf_wiredIV_isErgodic_of_boxCap hp hp1 hcap


-- created on 2026-10-23
