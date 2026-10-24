import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.wpdprimaldegree
open Finset Set SimpleGraph StatMech StatMech.Lattice


/--
[wpd_signStep_up_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpdprimaldegree.lean)
-/
@[path]
private lemma wpd_signStep_up_iff_eq
  {z u v : Site 2} :
-- imply
  wnd_signStep z u v = 1 ↔ (u 0 = v 0 ∧ u 0 ≤ z 0 - 1) ∧ u 1 = z 1 - 1 ∧ v 1 = z 1 := by
-- proof
  apply StatMech.Lattice.wpd_signStep_up_iff z u v

/--
[wpd_signStep_down_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpdprimaldegree.lean)
-/
@[path]
private lemma wpd_signStep_down_iff_eq
  {z u v : Site 2} :
-- imply
  wnd_signStep z u v = -1 ↔ (u 0 = v 0 ∧ u 0 ≤ z 0 - 1) ∧ u 1 = z 1 ∧ v 1 = z 1 - 1 := by
-- proof
  apply StatMech.Lattice.wpd_signStep_down_iff z u v

/--
[wpd_signStep_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpdprimaldegree.lean)
-/
@[path]
private lemma wpd_signStep_dichotomy_eq
  {z u v : Site 2}
-- given
  (h : wnd_signStep z u v ≠ 0) :
-- imply
  ((u 0 = v 0 ∧ u 0 ≤ z 0 - 1) ∧ u 1 = z 1 - 1 ∧ v 1 = z 1) ∨ ((u 0 = v 0 ∧ u 0 ≤ z 0 - 1) ∧ u 1 = z 1 ∧ v 1 = z 1 - 1) := by
-- proof
  apply StatMech.Lattice.wpd_signStep_dichotomy z u v h

/--
[wpd_count_le_one_of_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpdprimaldegree.lean)
-/
@[path]
private lemma wpd_count_le_one_of_nodup_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {e : Sym2 (Site 2)}
-- given
  (hnd : Vc.edges.Nodup) :
-- imply
  Vc.edges.count e ≤ 1 := by
-- proof
  apply StatMech.Lattice.wpd_count_le_one_of_nodup Vc hnd e

/--
[wpd_simple_cross_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpdprimaldegree.lean)
-/
@[path]
private lemma wpd_simple_cross_le_one_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
  {c : ℤ}
-- given
  (hcyc : Vc.IsCycle) :
-- imply
  Vc.edges.count (rpc_hCrossEdge (![c, z 1] : Site 2)) ≤ 1 := by
-- proof
  apply StatMech.Lattice.wpd_simple_cross_le_one Vc hcyc z c

/--
[wpd_simple_cross_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpdprimaldegree.lean)
-/
@[path]
private lemma wpd_simple_cross_iff_eq
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
  {z : Site 2}
  {c : ℤ}
-- given
  (hcyc : Vc.IsCycle) :
-- imply
  wis_ind z Vc (c + 1) ≠ wis_ind z Vc c ↔ Vc.edges.count (rpc_hCrossEdge (![c, z 1] : Site 2)) = 1 := by
-- proof
  apply StatMech.Lattice.wpd_simple_cross_iff Vc hcyc z c

/--
[wpd_upEntersInterior_iff_orientationConsistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpdprimaldegree.lean)
-/
@[path]
private lemma wpd_upEntersInterior_iff_orientationConsistent_eq
  {z : Site 2}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a} :
-- imply
  wpd_UpEntersInterior z Vc ↔ wel_OrientationConsistent z Vc := by
-- proof
  apply StatMech.Lattice.wpd_upEntersInterior_iff_orientationConsistent z Vc

/--
[wpd_orientationConsistent_of_upEntersInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpdprimaldegree.lean)
-/
@[path]
private lemma wpd_orientationConsistent_of_upEntersInterior_eq
  {z : Site 2}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (h : wpd_UpEntersInterior z Vc) :
-- imply
  wel_OrientationConsistent z Vc := by
-- proof
  apply StatMech.Lattice.wpd_orientationConsistent_of_upEntersInterior z Vc h

/--
[wpd_signsAlternate_of_upEntersInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpdprimaldegree.lean)
-/
@[path]
private lemma wpd_signsAlternate_of_upEntersInterior_eq
  {z : Site 2}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (h : wpd_UpEntersInterior z Vc) :
-- imply
  wos_SignsAlternateInColumnOrder z Vc := by
-- proof
  apply StatMech.Lattice.wpd_signsAlternate_of_upEntersInterior z Vc h

/--
[wpd_columnAlternates_of_upEntersInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpdprimaldegree.lean)
-/
@[path]
private lemma wpd_columnAlternates_of_upEntersInterior_eq
  {z : Site 2}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (h : wpd_UpEntersInterior z Vc) :
-- imply
  wna_ColumnAlternates z Vc := by
-- proof
  apply StatMech.Lattice.wpd_columnAlternates_of_upEntersInterior z Vc h

/--
[wpd_signedCross_pm_one_of_upEntersInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpdprimaldegree.lean)
-/
@[path]
private lemma wpd_signedCross_pm_one_of_upEntersInterior_eq
  {z : Site 2}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (h : wpd_UpEntersInterior z Vc)
  (hodd : ¬ Even (jec_rayCount z Vc)) :
-- imply
  wnd_signedCross z Vc = 1 ∨ wnd_signedCross z Vc = -1 := by
-- proof
  apply StatMech.Lattice.wpd_signedCross_pm_one_of_upEntersInterior z Vc h hodd

/--
[wpd_upEntersInterior_of_alternate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpdprimaldegree.lean)
-/
@[path]
private lemma wpd_upEntersInterior_of_alternate_eq
  {z : Site 2}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (halt : wos_SignsAlternateInColumnOrder z Vc)
  (hlen : wos_IndicatorLenEq z Vc) :
-- imply
  wpd_UpEntersInterior z Vc := by
-- proof
  apply StatMech.Lattice.wpd_upEntersInterior_of_alternate z Vc halt hlen

/--
[wpd_upEntersInterior_iff_alternate_and_len](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpdprimaldegree.lean)
-/
@[path]
private lemma wpd_upEntersInterior_iff_alternate_and_len_eq
  {z : Site 2}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a} :
-- imply
  wpd_UpEntersInterior z Vc ↔ (wos_SignsAlternateInColumnOrder z Vc ∧ wos_IndicatorLenEq z Vc) := by
-- proof
  apply StatMech.Lattice.wpd_upEntersInterior_iff_alternate_and_len z Vc

/--
[wpd_unitSquare_upEntersInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpdprimaldegree.lean)
-/
@[path]
private lemma wpd_unitSquare_upEntersInterior_eq :
-- imply
  wpd_UpEntersInterior (![1, 1] : Site 2) wwit_unitSquareLoop := by
-- proof
  apply StatMech.Lattice.wpd_unitSquare_upEntersInterior

/--
[wpd_Ltromino_upEntersInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpdprimaldegree.lean)
-/
@[path]
private lemma wpd_Ltromino_upEntersInterior_eq :
-- imply
  wpd_UpEntersInterior (![1, 1] : Site 2) wnu_LtrominoLoop := by
-- proof
  apply StatMech.Lattice.wpd_Ltromino_upEntersInterior

/--
[wpd_doubleSquare_not_upEntersInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpdprimaldegree.lean)
-/
@[path]
private lemma wpd_doubleSquare_not_upEntersInterior_eq :
-- imply
  ¬ wpd_UpEntersInterior (![1, 1] : Site 2) wnu_doubleSquare := by
-- proof
  apply StatMech.Lattice.wpd_doubleSquare_not_upEntersInterior


-- created on 2026-10-23
