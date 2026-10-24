import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.StarHullWinding
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[shw_vertStep_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullWinding.lean)
-/
@[path]
private lemma shw_vertStep_right_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hd : e.dir = ![1, 0]) :
-- imply
  (dartFace e) 0 = (dartFace (dartNext K e)) 0 := by
-- proof
  apply StatMech.Lattice.shw_vertStep_right K e hd

/--
[shw_vertStep_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullWinding.lean)
-/
@[path]
private lemma shw_vertStep_left_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hd : e.dir = ![-1, 0]) :
-- imply
  (dartFace e) 0 = (dartFace (dartNext K e)) 0 := by
-- proof
  apply StatMech.Lattice.shw_vertStep_left K e hd

/--
[shw_vertStep_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullWinding.lean)
-/
@[path]
private lemma shw_vertStep_dir_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hv : (dartFace e) 0 = (dartFace (dartNext K e)) 0) :
-- imply
  e.dir = ![1, 0] ∨ e.dir = ![-1, 0] := by
-- proof
  apply StatMech.Lattice.shw_vertStep_dir K e hv

/--
[shw_extremeCell_eq_tail_of_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullWinding.lean)
-/
@[path]
private lemma shw_extremeCell_eq_tail_of_left_eq
  {e : Dart}
-- given
  (hd : e.dir = ![-1, 0]) :
-- imply
  (![dartFace e 0 + 1, dartFace e 1 + 1] : Site 2) = e.tail := by
-- proof
  apply StatMech.Lattice.shw_extremeCell_eq_tail_of_left e hd

/--
[shw_extremeCell_mem_of_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullWinding.lean)
-/
@[path]
private lemma shw_extremeCell_mem_of_left_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e)
  (hd : e.dir = ![-1, 0]) :
-- imply
  (![dartFace e 0 + 1, dartFace e 1 + 1] : Site 2) ∈ K := by
-- proof
  apply StatMech.Lattice.shw_extremeCell_mem_of_left he hd

/--
[shw_extremeCell_notMem_of_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullWinding.lean)
-/
@[path]
private lemma shw_extremeCell_notMem_of_right_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e)
  (hd : e.dir = ![1, 0]) :
-- imply
  (![dartFace e 0 + 1, dartFace e 1] : Site 2) ∉ K := by
-- proof
  apply StatMech.Lattice.shw_extremeCell_notMem_of_right he hd

/--
[shw_mpl_edges_form](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullWinding.lean)
-/
@[path]
private lemma shw_mpl_edges_form_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (mpl_orbitLoop K a).edges = (List.range (dartOrbitPeriod K a)).map (fun k => s(dartFace ((dartNext K)^[k] a.1), dartFace ((dartNext K)^[k + 1] a.1))) := by
-- proof
  apply StatMech.Lattice.shw_mpl_edges_form K a

/--
[shw_exists_vertStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullWinding.lean)
-/
@[path]
private lemma shw_exists_vertStep_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hcyc : (mpl_orbitLoop K a).IsCycle) :
-- imply
  ∃ k < dartOrbitPeriod K a, (dartFace ((dartNext K)^[k] a.1)) 0 = (dartFace ((dartNext K)^[k + 1] a.1)) 0 := by
-- proof
  apply StatMech.Lattice.shw_exists_vertStep K a hcyc

/--
[shw_minCol_le_of_vertEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullWinding.lean)
-/
@[path]
private lemma shw_minCol_le_of_vertEdge_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {c : ℤ}
  {x y : Site 2}
-- given
  (hmin : ∀ k < dartOrbitPeriod K a, (dartFace ((dartNext K)^[k] a.1)) 0 = (dartFace ((dartNext K)^[k + 1] a.1)) 0 → c ≤ (dartFace ((dartNext K)^[k] a.1)) 0)
  (hxy : s(x, y) ∈ (mpl_orbitLoop K a).edges)
  (hcol : x 0 = y 0) :
-- imply
  c ≤ x 0 := by
-- proof
  apply StatMech.Lattice.shw_minCol_le_of_vertEdge K a c hmin hxy hcol

/--
[shw_minVertStep_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullWinding.lean)
-/
@[path]
private lemma shw_minVertStep_exists_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hcyc : (mpl_orbitLoop K a).IsCycle) :
-- imply
  ∃ k < dartOrbitPeriod K a, ((dartFace ((dartNext K)^[k] a.1)) 0 = (dartFace ((dartNext K)^[k + 1] a.1)) 0) ∧ (∀ j < dartOrbitPeriod K a, (dartFace ((dartNext K)^[j] a.1)) 0 = (dartFace ((dartNext K)^[j + 1] a.1)) 0 → (dartFace ((dartNext K)^[k] a.1)) 0 ≤ (dartFace ((dartNext K)^[j] a.1)) 0) := by
-- proof
  apply StatMech.Lattice.shw_minVertStep_exists K a hcyc

/--
[shw_windingWitness_of_minLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullWinding.lean)
-/
@[path]
private lemma shw_windingWitness_of_minLeft_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hcyc : (mpl_orbitLoop K a).IsCycle)
  (hres : shw_MinVertStepLeft K a) :
-- imply
  wei_WindingWitness K a := by
-- proof
  apply StatMech.Lattice.shw_windingWitness_of_minLeft K a hcyc hres

/--
[shw_starHull_mpl_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullWinding.lean)
-/
@[path]
private lemma shw_starHull_mpl_isCycle_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod (ndt_StarHull K) a) :
-- imply
  (mpl_orbitLoop (ndt_StarHull K) a).IsCycle := by
-- proof
  apply StatMech.Lattice.shw_starHull_mpl_isCycle K a hp

/--
[shw_starHull_windingWitness_of_minLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullWinding.lean)
-/
@[path]
private lemma shw_starHull_windingWitness_of_minLeft_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod (ndt_StarHull K) a)
  (hres : shw_MinVertStepLeft (ndt_StarHull K) a) :
-- imply
  wei_WindingWitness (ndt_StarHull K) a := by
-- proof
  apply StatMech.Lattice.shw_starHull_windingWitness_of_minLeft K a hp hres

/--
[shw_unitCell_faceInj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullWinding.lean)
-/
@[path]
private lemma shw_unitCell_faceInj_eq :
-- imply
  Set.InjOn (fun k => dartFace ((dartNext unitCell)^[k] ucBase.1)) (Set.Iio (dartOrbitPeriod unitCell ucBase)) := by
-- proof
  apply StatMech.Lattice.shw_unitCell_faceInj

/--
[shw_unitCell_minVertStepLeft](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullWinding.lean)
-/
@[path]
private lemma shw_unitCell_minVertStepLeft_eq :
-- imply
  shw_MinVertStepLeft unitCell ucBase := by
-- proof
  apply StatMech.Lattice.shw_unitCell_minVertStepLeft

/--
[shw_unitCell_windingWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullWinding.lean)
-/
@[path]
private lemma shw_unitCell_windingWitness_eq :
-- imply
  wei_WindingWitness unitCell ucBase := by
-- proof
  apply StatMech.Lattice.shw_unitCell_windingWitness

/--
[shw_kingSat_excludes_diagSubcase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/StarHullWinding.lean)
-/
@[path]
private lemma shw_kingSat_excludes_diagSubcase_eq
  {K : Set (Site 2)}
  {e : Dart}
  {c r : ℤ}
-- given
  (hK : npd_NoDiagTouch K)
  (he : IsBoundaryDart K e)
  (hd : e.dir = ![1, 0])
  (hc : c = dartFace e 0)
  (hr : r + 1 = dartFace e 1) :
-- imply
  ¬ ((![c + 1, r] : Site 2) ∈ K ∧ (![c, r] : Site 2) ∉ K) := by
-- proof
  apply StatMech.Lattice.shw_kingSat_excludes_diagSubcase hK he hd c r hc hr


-- created on 2026-10-23
