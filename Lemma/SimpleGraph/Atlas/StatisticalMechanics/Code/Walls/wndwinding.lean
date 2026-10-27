import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.wndwinding.Part3
open Finset Set SimpleGraph StatMech StatMech.Lattice


/--
[wnd_signStep_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wndwinding.lean)
-/
@[path]
private lemma wnd_signStep_mem_eq
  {z u v : Site 2} :
-- imply
  wnd_signStep z u v = 1 ∨ wnd_signStep z u v = 0 ∨ wnd_signStep z u v = -1 := by
-- proof
  apply StatMech.Lattice.wnd_signStep_mem z u v

/--
[wnd_abs_signStep_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wndwinding.lean)
-/
@[path]
private lemma wnd_abs_signStep_le_one_eq
  {z u v : Site 2} :
-- imply
  |wnd_signStep z u v| ≤ 1 := by
-- proof
  apply StatMech.Lattice.wnd_abs_signStep_le_one z u v

/--
[wnd_signStep_ne_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wndwinding.lean)
-/
@[path]
private lemma wnd_signStep_ne_zero_iff_eq
  {z u v : Site 2} :
-- imply
  wnd_signStep z u v ≠ 0 ↔ jec_rayEdge z s(u, v) := by
-- proof
  apply StatMech.Lattice.wnd_signStep_ne_zero_iff z u v

/--
[wnd_abs_signStep_eq_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wndwinding.lean)
-/
@[path]
private lemma wnd_abs_signStep_eq_indicator_eq
  {z u v : Site 2} :
-- imply
  |wnd_signStep z u v| = (if jec_rayEdge z s(u, v) then 1 else 0) := by
-- proof
  apply StatMech.Lattice.wnd_abs_signStep_eq_indicator z u v

/--
[wnd_signStep_parity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wndwinding.lean)
-/
@[path]
private lemma wnd_signStep_parity_eq
  {z u v : Site 2} :
-- imply
  wnd_signStep z u v % 2 = (if jec_rayEdge z s(u, v) then (1 : ℤ) else 0) % 2 := by
-- proof
  apply StatMech.Lattice.wnd_signStep_parity z u v

/--
[wnd_signStep_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wndwinding.lean)
-/
@[path]
private lemma wnd_signStep_swap_eq
  {z u v : Site 2} :
-- imply
  wnd_signStep z v u = - wnd_signStep z u v := by
-- proof
  apply StatMech.Lattice.wnd_signStep_swap z u v

/--
[wnd_signedCross_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wndwinding.lean)
-/
@[path]
private lemma wnd_signedCross_nil_eq
  {z x : Site 2} :
-- imply
  wnd_signedCross z (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk x x) = 0 := by
-- proof
  apply StatMech.Lattice.wnd_signedCross_nil z x

/--
[wnd_signedCross_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wndwinding.lean)
-/
@[path]
private lemma wnd_signedCross_append_eq
  {z : Site 2}
  {x y w' : Site 2}
  {p : (hypercubicLattice 2).Walk x y}
  {q : (hypercubicLattice 2).Walk y w'} :
-- imply
  wnd_signedCross z (p.append q) = wnd_signedCross z p + wnd_signedCross z q := by
-- proof
  apply StatMech.Lattice.wnd_signedCross_append z p q

/--
[wnd_signedCross_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wndwinding.lean)
-/
@[path]
private lemma wnd_signedCross_reverse_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y} :
-- imply
  wnd_signedCross z w.reverse = - wnd_signedCross z w := by
-- proof
  apply StatMech.Lattice.wnd_signedCross_reverse z w

/--
[wnd_rayCount_eq_darts_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wndwinding.lean)
-/
@[path]
private lemma wnd_rayCount_eq_darts_sum_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y} :
-- imply
  (jec_rayCount z w : ℤ) = (w.darts.map (fun d => if jec_rayEdge z d.edge then (1 : ℤ) else 0)).sum := by
-- proof
  apply StatMech.Lattice.wnd_rayCount_eq_darts_sum z w

/--
[wnd_signedCross_abs_le_rayCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wndwinding.lean)
-/
@[path]
private lemma wnd_signedCross_abs_le_rayCount_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y} :
-- imply
  |wnd_signedCross z w| ≤ (jec_rayCount z w : ℤ) := by
-- proof
  apply StatMech.Lattice.wnd_signedCross_abs_le_rayCount z w

/--
[wnd_signedCross_parity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wndwinding.lean)
-/
@[path]
private lemma wnd_signedCross_parity_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y} :
-- imply
  wnd_signedCross z w % 2 = (jec_rayCount z w : ℤ) % 2 := by
-- proof
  apply StatMech.Lattice.wnd_signedCross_parity z w

/--
[wnd_signedCross_ne_zero_of_rayCount_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wndwinding.lean)
-/
@[path]
private lemma wnd_signedCross_ne_zero_of_rayCount_odd_eq
  {z : Site 2}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hodd : ¬ Even (jec_rayCount z w)) :
-- imply
  wnd_signedCross z w ≠ 0 := by
-- proof
  apply StatMech.Lattice.wnd_signedCross_ne_zero_of_rayCount_odd z w hodd

/--
[wnd_orbitLoop_signedCross_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wndwinding.lean)
-/
@[path]
private lemma wnd_orbitLoop_signedCross_ne_zero_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z : Site 2}
-- given
  (hK : K.Finite)
  (hodd : ¬ Even (jec_rayCount z (olb_orbitLoop K hK a.1 a.2))) :
-- imply
  wnd_signedCross z (olb_orbitLoop K hK a.1 a.2) ≠ 0 := by
-- proof
  apply StatMech.Lattice.wnd_orbitLoop_signedCross_ne_zero K hK a z hodd

/--
[wnd_revCount_ne_zero_of_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wndwinding.lean)
-/
@[path]
private lemma wnd_revCount_ne_zero_of_bridge_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z : Site 2}
-- given
  (hK : K.Finite)
  (hbridge : wnd_SignedCrossEqRevCount K hK a z)
  (hodd : ¬ Even (jec_rayCount z (olb_orbitLoop K hK a.1 a.2))) :
-- imply
  revCount K a ≠ 0 := by
-- proof
  apply StatMech.Lattice.wnd_revCount_ne_zero_of_bridge K hK a z hbridge hodd

/--
[wnd_revCount_pm_one_of_residues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wndwinding.lean)
-/
@[path]
private lemma wnd_revCount_pm_one_of_residues_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z : Site 2}
-- given
  (hK : K.Finite)
  (hbridge : wnd_SignedCrossEqRevCount K hK a z)
  (hpm : wnd_SignedCrossPMone K hK a z) :
-- imply
  revCount K a = 1 ∨ revCount K a = -1 := by
-- proof
  apply StatMech.Lattice.wnd_revCount_pm_one_of_residues K hK a z hbridge hpm

/--
[wnd_eulerCharOne_of_residues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wndwinding.lean)
-/
@[path]
private lemma wnd_eulerCharOne_of_residues_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {z : Site 2}
-- given
  (hK : K.Finite)
  (hp : 3 ≤ dartOrbitPeriod K a)
  (hbridge : wnd_SignedCrossEqRevCount K hK a z)
  (hpm : wnd_SignedCrossPMone K hK a z) :
-- imply
  EulerCharOne K a := by
-- proof
  apply StatMech.Lattice.wnd_eulerCharOne_of_residues K hK a z hp hbridge hpm

/--
[wnd_unitSquareLoop_signedCross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wndwinding.lean)
-/
@[path]
private lemma wnd_unitSquareLoop_signedCross_eq :
-- imply
  wnd_signedCross (![1, 1] : Site 2) wwit_unitSquareLoop = 1 := by
-- proof
  apply StatMech.Lattice.wnd_unitSquareLoop_signedCross

/--
[wnd_unitSquareLoop_signedCross_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wndwinding.lean)
-/
@[path]
private lemma wnd_unitSquareLoop_signedCross_ne_zero_eq :
-- imply
  wnd_signedCross (![1, 1] : Site 2) wwit_unitSquareLoop ≠ 0 := by
-- proof
  apply StatMech.Lattice.wnd_unitSquareLoop_signedCross_ne_zero


-- created on 2026-10-23
