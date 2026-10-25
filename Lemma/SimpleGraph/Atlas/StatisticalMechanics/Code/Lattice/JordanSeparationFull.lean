import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanSeparationFull
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[jsf_bdEdgeMatch_of_rayParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationFull.lean)
-/
@[path]
private lemma jsf_bdEdgeMatch_of_rayParity_eq
  {K : Set (Site 2)}
  {a : Site 2}
  {Vc : (hypercubicLattice 2).Walk a a}
-- given
  (hin : ∀ z, z ∈ K → ¬ Even (jec_rayCount z Vc))
  (hout : ∀ z, z ∉ K → Even (jec_rayCount z Vc)) :
-- imply
  pww_BdEdgeMatch K Vc := by
-- proof
  apply StatMech.Lattice.jsf_bdEdgeMatch_of_rayParity Vc hin hout

/--
[jsf_unitCell_loop_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationFull.lean)
-/
@[path]
private lemma jsf_unitCell_loop_edges_eq :
-- imply
  (mpl_orbitLoop unitCell ucBase).edges = [s((![0, 0] : Site 2), ![0, -1]), s((![0, -1] : Site 2), ![-1, -1]), s((![-1, -1] : Site 2), ![-1, 0]), s((![-1, 0] : Site 2), ![0, 0])] := by
-- proof
  apply StatMech.Lattice.jsf_unitCell_loop_edges

/--
[jsf_unitCell_rayCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationFull.lean)
-/
@[path]
private lemma jsf_unitCell_rayCount_eq
  {z : Site 2} :
-- imply
  jec_rayCount z (mpl_orbitLoop unitCell ucBase) = (if z 1 = 0 ∧ 1 ≤ z 0 then 1 else 0) + (if z 1 = 0 ∧ 0 ≤ z 0 then 1 else 0) := by
-- proof
  apply StatMech.Lattice.jsf_unitCell_rayCount z

/--
[jsf_unitCell_inside_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationFull.lean)
-/
@[path]
private lemma jsf_unitCell_inside_odd_eq
  {z : Site 2}
-- given
  (hz : z ∈ unitCell) :
-- imply
  ¬ Even (jec_rayCount z (mpl_orbitLoop unitCell ucBase)) := by
-- proof
  apply StatMech.Lattice.jsf_unitCell_inside_odd z hz

/--
[jsf_unitCell_outside_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationFull.lean)
-/
@[path]
private lemma jsf_unitCell_outside_even_eq
  {z : Site 2}
-- given
  (hz : z ∉ unitCell) :
-- imply
  Even (jec_rayCount z (mpl_orbitLoop unitCell ucBase)) := by
-- proof
  apply StatMech.Lattice.jsf_unitCell_outside_even z hz

/--
[jsf_unitCell_eq_leftRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationFull.lean)
-/
@[path]
private lemma jsf_unitCell_eq_leftRegion_eq :
-- imply
  unitCell = jec_leftRegion (mpl_orbitLoop unitCell ucBase) := by
-- proof
  apply StatMech.Lattice.jsf_unitCell_eq_leftRegion

/--
[jsf_unitCell_loop_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationFull.lean)
-/
@[path]
private lemma jsf_unitCell_loop_isCycle_eq :
-- imply
  (mpl_orbitLoop unitCell ucBase).IsCycle := by
-- proof
  apply StatMech.Lattice.jsf_unitCell_loop_isCycle

/--
[jsf_unitCell_bdEdgeMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationFull.lean)
-/
@[path]
private lemma jsf_unitCell_bdEdgeMatch_eq :
-- imply
  pww_BdEdgeMatch unitCell (mpl_orbitLoop unitCell ucBase) := by
-- proof
  apply StatMech.Lattice.jsf_unitCell_bdEdgeMatch

/--
[jsf_unitCell_fillClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationFull.lean)
-/
@[path]
private lemma jsf_unitCell_fillClosed_eq :
-- imply
  ndt_FillClosed unitCell := by
-- proof
  apply StatMech.Lattice.jsf_unitCell_fillClosed

/--
[jsf_starHull_unitCell_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationFull.lean)
-/
@[path]
private lemma jsf_starHull_unitCell_eq_eq :
-- imply
  ndt_StarHull unitCell = unitCell := by
-- proof
  apply StatMech.Lattice.jsf_starHull_unitCell_eq

/--
[jsf_starHull_unitCell_bdEdgeMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationFull.lean)
-/
@[path]
private lemma jsf_starHull_unitCell_bdEdgeMatch_eq :
-- imply
  pww_BdEdgeMatch (ndt_StarHull unitCell) (mpl_orbitLoop unitCell ucBase) := by
-- proof
  apply StatMech.Lattice.jsf_starHull_unitCell_bdEdgeMatch

/--
[jsf_starHull_bdEdgeMatch_of_rayParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSeparationFull.lean)
-/
@[path]
private lemma jsf_starHull_bdEdgeMatch_of_rayParity_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (hin : ∀ z, z ∈ ndt_StarHull K → ¬ Even (jec_rayCount z (mpl_orbitLoop (ndt_StarHull K) a)))
  (hout : ∀ z, z ∉ ndt_StarHull K → Even (jec_rayCount z (mpl_orbitLoop (ndt_StarHull K) a))) :
-- imply
  pww_BdEdgeMatch (ndt_StarHull K) (mpl_orbitLoop (ndt_StarHull K) a) := by
-- proof
  apply StatMech.Lattice.jsf_starHull_bdEdgeMatch_of_rayParity K a hin hout


-- created on 2026-10-23
