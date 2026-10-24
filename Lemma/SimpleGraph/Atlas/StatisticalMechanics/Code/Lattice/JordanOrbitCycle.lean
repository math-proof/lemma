import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Lattice.JordanOrbitCycle
open SimpleGraph Set Function StatMech StatMech.Lattice


/--
[joc_cycleSubgraph_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOrbitCycle.lean)
-/
@[path]
private lemma joc_cycleSubgraph_connected_eq
  {v : Site 2}
  {c : (hypercubicLattice 2).Walk v v}
-- given
  (hc : c.IsCycle) :
-- imply
  (joc_cycleSubgraph c hc).G.Connected := by
-- proof
  apply StatMech.Lattice.joc_cycleSubgraph_connected c hc

/--
[joc_cycle_edge_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOrbitCycle.lean)
-/
@[path]
private lemma joc_cycle_edge_card_eq
  {v : Site 2}
  {c : (hypercubicLattice 2).Walk v v}
-- given
  (hc : c.IsCycle) :
-- imply
  (joc_cycleSubgraph c hc).G.edgeSet.ncard = c.length := by
-- proof
  apply StatMech.Lattice.joc_cycle_edge_card c hc

/--
[joc_cycle_vert_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOrbitCycle.lean)
-/
@[path]
private lemma joc_cycle_vert_card_eq
  {v : Site 2}
  {c : (hypercubicLattice 2).Walk v v}
-- given
  (hc : c.IsCycle) :
-- imply
  Nat.card (joc_cycleSubgraph c hc).V = c.length := by
-- proof
  apply StatMech.Lattice.joc_cycle_vert_card c hc

/--
[joc_cycle_nullity_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOrbitCycle.lean)
-/
@[path]
private lemma joc_cycle_nullity_one_eq
  {v : Site 2}
  {c : (hypercubicLattice 2).Walk v v}
-- given
  (hc : c.IsCycle) :
-- imply
  nullity (joc_cycleSubgraph c hc).G = 1 := by
-- proof
  apply StatMech.Lattice.joc_cycle_nullity_one c hc

/--
[joc_cycle_uniqueBoundedRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOrbitCycle.lean)
-/
@[path]
private lemma joc_cycle_uniqueBoundedRegion_eq
  {v : Site 2}
  {c : (hypercubicLattice 2).Walk v v}
-- given
  (hc : c.IsCycle) :
-- imply
  Nat.card (jcb_BoundedRegion (joc_cycleSubgraph c hc)) = 1 := by
-- proof
  apply StatMech.Lattice.joc_cycle_uniqueBoundedRegion c hc

/--
[joc_orbitLoop_uniqueBoundedRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOrbitCycle.lean)
-/
@[path]
private lemma joc_orbitLoop_uniqueBoundedRegion_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a)
  (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a))) :
-- imply
  Nat.card (jcb_BoundedRegion (joc_cycleSubgraph (mpl_orbitLoop K a) (mpl_orbitLoop_isCycle K a hp hinj))) = 1 := by
-- proof
  apply StatMech.Lattice.joc_orbitLoop_uniqueBoundedRegion K a hp hinj

/--
[joc_faceInjOn_of_kingSaturated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOrbitCycle.lean)
-/
@[path]
private lemma joc_faceInjOn_of_kingSaturated_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hks : npm_KingSaturated K) :
-- imply
  Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a)) := by
-- proof
  apply StatMech.Lattice.joc_faceInjOn_of_kingSaturated K a hks

/--
[joc_kingSaturated_orbitLoop_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOrbitCycle.lean)
-/
@[path]
private lemma joc_kingSaturated_orbitLoop_isCycle_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a)
  (hks : npm_KingSaturated K) :
-- imply
  (mpl_orbitLoop K a).IsCycle := by
-- proof
  apply StatMech.Lattice.joc_kingSaturated_orbitLoop_isCycle K a hp hks

/--
[joc_kingSaturated_orbit_uniqueBoundedRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOrbitCycle.lean)
-/
@[path]
private lemma joc_kingSaturated_orbit_uniqueBoundedRegion_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hp : 3 ≤ dartOrbitPeriod K a)
  (hks : npm_KingSaturated K) :
-- imply
  Nat.card (jcb_BoundedRegion (joc_cycleSubgraph (mpl_orbitLoop K a) (joc_kingSaturated_orbitLoop_isCycle K a hp hks))) = 1 := by
-- proof
  apply StatMech.Lattice.joc_kingSaturated_orbit_uniqueBoundedRegion K a hp hks

/--
[joc_unitCell_kingSaturated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOrbitCycle.lean)
-/
@[path]
private lemma joc_unitCell_kingSaturated_eq :
-- imply
  npm_KingSaturated unitCell := by
-- proof
  apply StatMech.Lattice.joc_unitCell_kingSaturated

/--
[joc_unitCell_orbit_uniqueBoundedRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOrbitCycle.lean)
-/
@[path]
private lemma joc_unitCell_orbit_uniqueBoundedRegion_eq :
-- imply
  Nat.card (jcb_BoundedRegion (joc_cycleSubgraph (mpl_orbitLoop unitCell ucBase) (joc_kingSaturated_orbitLoop_isCycle unitCell ucBase (by rw [unitCell_orbitPeriod_eq_four]; norm_num) joc_unitCell_kingSaturated))) = 1 := by
-- proof
  apply StatMech.Lattice.joc_unitCell_orbit_uniqueBoundedRegion

/--
[joc_domino_kingSaturated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOrbitCycle.lean)
-/
@[path]
private lemma joc_domino_kingSaturated_eq :
-- imply
  npm_KingSaturated domino := by
-- proof
  apply StatMech.Lattice.joc_domino_kingSaturated

/--
[joc_domino_orbit_uniqueBoundedRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOrbitCycle.lean)
-/
@[path]
private lemma joc_domino_orbit_uniqueBoundedRegion_eq :
-- imply
  Nat.card (jcb_BoundedRegion (joc_cycleSubgraph (mpl_orbitLoop domino dmBase) (joc_kingSaturated_orbitLoop_isCycle domino dmBase (by rw [domino_orbitPeriod_eq_six]; norm_num) joc_domino_kingSaturated))) = 1 := by
-- proof
  apply StatMech.Lattice.joc_domino_orbit_uniqueBoundedRegion

/--
[joc_Ltromino_kingSaturated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOrbitCycle.lean)
-/
@[path]
private lemma joc_Ltromino_kingSaturated_eq :
-- imply
  npm_KingSaturated joc_Ltromino := by
-- proof
  apply StatMech.Lattice.joc_Ltromino_kingSaturated

/--
[joc_Ltromino_faceMultiplicityOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOrbitCycle.lean)
-/
@[path]
private lemma joc_Ltromino_faceMultiplicityOne_eq
  {a : {e : Dart // IsBoundaryDart joc_Ltromino e}} :
-- imply
  usc_FaceMultiplicityOne joc_Ltromino a := by
-- proof
  apply StatMech.Lattice.joc_Ltromino_faceMultiplicityOne a

/--
[joc_diagK_diagTouch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOrbitCycle.lean)
-/
@[path]
private lemma joc_diagK_diagTouch_eq :
-- imply
  npd_DiagTouch jcb_diagK (![0, 0] : Site 2) := by
-- proof
  apply StatMech.Lattice.joc_diagK_diagTouch

/--
[joc_diagK_not_kingSaturated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOrbitCycle.lean)
-/
@[path]
private lemma joc_diagK_not_kingSaturated_eq :
-- imply
  ¬ npm_KingSaturated jcb_diagK := by
-- proof
  apply StatMech.Lattice.joc_diagK_not_kingSaturated

/--
[joc_pinch_forces_diagTouch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOrbitCycle.lean)
-/
@[path]
private lemma joc_pinch_forces_diagTouch_eq
  {K : Set (Site 2)}
  {e₁ e₂ : Dart}
-- given
  (he₁ : IsBoundaryDart K e₁)
  (he₂ : IsBoundaryDart K e₂)
  (hface : dartFace e₁ = dartFace e₂)
  (hdir : e₁.dir ≠ e₂.dir) :
-- imply
  npd_DiagTouch K (dartFace e₁) := by
-- proof
  apply StatMech.Lattice.joc_pinch_forces_diagTouch he₁ he₂ hface hdir

/--
[joc_noLocalPinch_of_kingSaturated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOrbitCycle.lean)
-/
@[path]
private lemma joc_noLocalPinch_of_kingSaturated_eq
  {K : Set (Site 2)}
  {e₁ e₂ : Dart}
-- given
  (hks : npm_KingSaturated K)
  (he₁ : IsBoundaryDart K e₁)
  (he₂ : IsBoundaryDart K e₂)
  (hface : dartFace e₁ = dartFace e₂) :
-- imply
  e₁.dir = e₂.dir := by
-- proof
  apply StatMech.Lattice.joc_noLocalPinch_of_kingSaturated hks he₁ he₂ hface

/--
[joc_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOrbitCycle.lean)
-/
@[path]
private lemma joc_status_eq :
-- imply
  (∀ (v : Site 2) (c : (hypercubicLattice 2).Walk v v) (hc : c.IsCycle), Nat.card (jcb_BoundedRegion (joc_cycleSubgraph c hc)) = 1) ∧ (∀ (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}), npm_KingSaturated K → Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a))) ∧ (∀ (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}), 3 ≤ dartOrbitPeriod K a → npm_KingSaturated K → (mpl_orbitLoop K a).IsCycle) ∧ ¬ npm_KingSaturated jcb_diagK ∧ npd_DiagTouch jcb_diagK (![0, 0] : Site 2) := by
-- proof
  apply StatMech.Lattice.joc_status


-- created on 2026-10-23
